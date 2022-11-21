use std::collections::{HashMap, HashSet};

use lazy_static::lazy_static;
use swc_ecma_ast::TsTypeParamDecl;
use syn::{
    parse_quote, parse_str, punctuated::Punctuated, token::Colon2, visit::Visit,
    visit_mut::VisitMut, AngleBracketedGenericArguments, Attribute, Expr, ExprAssign, ExprPath,
    FnArg, ForeignItem, GenericArgument, Ident, ItemUse, PatType, PathArguments, PathSegment,
    ReturnType, Token, Type, TypePath, TypeReference, TypeSlice, UseName, UseRename,
};

use crate::wasm::{extends, js_value, merge_attrs, method_of};

/// Makes a JS ident a valid Rust ident.
/// Also changes casing to match [web_sys] & [js_sys].
pub fn sanitize_sym(sym: &str) -> Ident {
    let ident = match sym {
        "self" | "super" | "crate" => format!("{sym}_rs"),
        _ => {
            let mut sanitized_sym = String::new();
            let mut prev_cap = false;
            let mut next_it = sym.chars().skip(1);
            let all_upper = sym
                .chars()
                .all(|c| !c.is_ascii_alphabetic() || c.is_ascii_uppercase());
            for c in sym.chars() {
                let next = next_it.next();
                sanitized_sym.push(
                    if !all_upper && prev_cap && next.map_or(true, |next| next.is_ascii_uppercase())
                    {
                        c.to_ascii_lowercase()
                    } else {
                        c
                    },
                );
                prev_cap = c.is_ascii_uppercase() || c.is_ascii_digit();
            }
            sanitized_sym
        }
    };
    parse_str(&ident)
        .or_else(|_| parse_str(&format!("r#{ident}")))
        .expect(&ident)
}

pub fn import_prefix_to_idents(path: &str) -> Vec<Ident> {
    let mut acc = vec![];
    let mut first_dot_dot = true;
    for seg in path.split('/') {
        if seg == "." {
            acc.push(<Token!(super)>::default().into());
        } else if seg == ".." {
            acc.push(<Token!(super)>::default().into());
            if first_dot_dot {
                acc.push(<Token!(super)>::default().into());
                first_dot_dot = false;
            }
        } else {
            let seg = format!("{}Mod", seg.strip_suffix(".js").unwrap_or(seg));
            acc.push(parse_str(&seg).unwrap());
        }
    }

    acc
}

pub fn import_path_to_type_path_prefix(path: &str) -> Punctuated<PathSegment, Colon2> {
    let mut acc = Punctuated::new();
    let mut first_dot_dot = true;
    for seg in path.split('/') {
        if seg == "." {
            acc.push(<Token!(super)>::default().into());
        } else if seg == ".." {
            acc.push(<Token!(super)>::default().into());
            if first_dot_dot {
                acc.push(<Token!(super)>::default().into());
                first_dot_dot = false;
            }
        } else {
            let seg = format!("{}Mod", seg.strip_suffix(".js").unwrap_or(seg));
            acc.push(parse_str(&seg).expect(&seg));
        }
    }

    acc
}

/// Various binding cleanup steps:
/// * Remove unnecessary parentheses around types
/// * Flatten `Option<Option<_>>`
/// * Replace known TypeScript string union types with string
/// * Make `Option<JsValue>` `JsValue`
pub struct BindingsCleaner;

impl VisitMut for BindingsCleaner {
    fn visit_foreign_item_mut(&mut self, fi: &mut ForeignItem) {
        merge_attrs(fi);
        match fi {
            ForeignItem::Fn(f) => self.visit_foreign_item_fn_mut(f),
            ForeignItem::Static(s) => self.visit_foreign_item_static_mut(s),
            ForeignItem::Type(t) => self.visit_foreign_item_type_mut(t),
            ForeignItem::Macro(m) => self.visit_foreign_item_macro_mut(m),
            ForeignItem::Verbatim(_) | _ => {}
        }
    }

    fn visit_type_mut(&mut self, t: &mut Type) {
        match t {
            Type::Array(t) => self.visit_type_array_mut(t),
            Type::BareFn(t) => self.visit_type_bare_fn_mut(t),
            Type::Group(t) => self.visit_type_group_mut(t),
            Type::ImplTrait(t) => self.visit_type_impl_trait_mut(t),
            Type::Infer(t) => self.visit_type_infer_mut(t),
            Type::Macro(t) => self.visit_type_macro_mut(t),
            Type::Never(t) => self.visit_type_never_mut(t),
            Type::Paren(p) => {
                let t_inner: &Type = &p.elem;
                *t = t_inner.clone();
                self.visit_type_mut(t);
            }
            Type::Path(t) => self.visit_type_path_mut(t),
            Type::Ptr(t) => self.visit_type_ptr_mut(t),
            Type::Reference(t) => self.visit_type_reference_mut(t),
            Type::Slice(t) => self.visit_type_slice_mut(t),
            Type::TraitObject(t) => self.visit_type_trait_object_mut(t),
            Type::Tuple(t) => self.visit_type_tuple_mut(t),
            other => todo!("{other:?}"),
        }
    }

    fn visit_type_path_mut(&mut self, t: &mut TypePath) {
        if t.path.leading_colon.is_some() {
            let seg = t.path.segments.last().unwrap();
            if seg.ident == "Option" {
                if let PathArguments::AngleBracketed(AngleBracketedGenericArguments {
                    args, ..
                }) = &seg.arguments
                {
                    if let GenericArgument::Type(Type::Path(
                        inner @ TypePath {
                            path: inner_path, ..
                        },
                    )) = args.first().unwrap()
                    {
                        if inner_path.leading_colon.is_some() {
                            let last = &inner_path.segments.last().unwrap().ident;
                            if last == "Option" || last == "JsValue" {
                                *t = inner.clone();
                            }
                        }
                    }
                }
            }
        } else if t.path.segments.len() == 1 {
            let seg = t.path.segments.first_mut().unwrap();
            let seg_ident_string = seg.ident.to_string();
            if KNOWN_STRING_TYPES.contains(&seg_ident_string.as_str()) {
                *t = parse_quote!(::std::string::String);
            }
        }
        // Make sure we visit T in Option<T>
        for seg in &mut t.path.segments {
            self.visit_path_segment_mut(seg);
        }
    }
}

/// Removes the given generics
pub struct ByeByeGenerics(pub Vec<Ident>);

impl ByeByeGenerics {
    pub fn new<'a>(args: impl Iterator<Item = &'a Box<TsTypeParamDecl>>) -> Self {
        Self(
            args.flat_map(|tp| tp.params.iter())
                .map(|t| sanitize_sym(&t.name.sym))
                .collect(),
        )
    }

    pub fn join(mut self, other: &Self) -> Self {
        self.0.extend(other.0.iter().cloned());
        Self(self.0)
    }
}

impl VisitMut for ByeByeGenerics {
    fn visit_type_path_mut(&mut self, t: &mut TypePath) {
        if t.path.segments.len() == 1 {
            let seg = t.path.segments.first_mut().unwrap();
            if seg.arguments.is_empty() && self.0.contains(&seg.ident) {
                *t = js_value();
            }
        }
        // Make sure we visit T in Option<T>
        for seg in &mut t.path.segments {
            self.visit_path_segment_mut(seg);
        }
    }
}

/// * Dedupe items with the same name
/// * Replace Self with class name
#[derive(Default)]
pub struct ModuleBindingsCleaner(HashMap<Option<syn::Path>, HashSet<String>>);

impl VisitMut for ModuleBindingsCleaner {
    fn visit_signature_mut(&mut self, sig: &mut syn::Signature) {
        let class_type = if let Some(FnArg::Typed(PatType { ty, .. })) = sig.inputs.first() {
            if let Type::Reference(ty) = ty.as_ref() {
                ty.elem.as_ref()
            } else {
                return;
            }
        } else {
            return;
        };

        struct SelfToClass(Type);
        impl VisitMut for SelfToClass {
            fn visit_type_mut(&mut self, t: &mut Type) {
                if let Type::Path(tp) = t {
                    if tp.path.segments.len() == 1 {
                        let seg = tp.path.segments.first_mut().unwrap();
                        if seg.ident == "Self" && seg.arguments.is_empty() {
                            *t = self.0.clone();
                        }
                    }
                }
            }
        }

        let mut stc = SelfToClass(class_type.clone());
        stc.visit_signature_mut(sig);
    }

    fn visit_foreign_item_mut(&mut self, fi: &mut ForeignItem) {
        if let ForeignItem::Fn(func) = fi {
            self.visit_foreign_item_fn_mut(func);
        }

        let clazz = if let ForeignItem::Fn(ff) = fi {
            method_of(ff)
        } else {
            None
        };

        let (ident, attrs) = match fi {
            ForeignItem::Fn(f) => (&mut f.sig.ident, &mut f.attrs),
            ForeignItem::Static(s) => (&mut s.ident, &mut s.attrs),
            ForeignItem::Type(_) | ForeignItem::Verbatim(_) | ForeignItem::Macro(_) => return,
            other => todo!("{other:?}"),
        };
        let mut ident_string = ident.to_string();
        let mut counter = 1;

        let entries = self.0.entry(clazz).or_default();
        while entries.contains(&ident_string) {
            ident_string = format!("{ident}_{counter}");
            counter += 1;
        }
        if counter > 1 {
            *ident = parse_str(&ident_string).unwrap();
        }
        entries.insert(ident_string);
    }
}

/// Collects all the names exported by a module
#[derive(Default)]
pub struct CollectPubs(pub HashSet<String>);

impl<'ast> Visit<'ast> for CollectPubs {
    fn visit_use_name(&mut self, un: &'ast UseName) {
        self.0.insert(un.ident.to_string());
    }

    fn visit_use_rename(&mut self, rn: &'ast UseRename) {
        self.0.insert(rn.rename.to_string());
    }

    fn visit_foreign_item(&mut self, fi: &'ast ForeignItem) {
        match fi {
            ForeignItem::Fn(f) => {
                self.0.insert(f.sig.ident.to_string());
            }
            ForeignItem::Static(s) => {
                self.0.insert(s.ident.to_string());
            }
            ForeignItem::Type(t) => {
                self.0.insert(t.ident.to_string());
            }
            _ => {}
        }
    }
}

/// Adds uses for [web_sys] or [js_sys] based on known names
pub struct SysUseAdder {
    /// Items that the module exports
    pub pubs: HashSet<String>,
    pub uses: HashSet<ItemUse>,
}

impl<'ast> Visit<'ast> for SysUseAdder {
    fn visit_type_path(&mut self, t: &'ast TypePath) {
        if t.path.segments.len() == 1 {
            let seg = t.path.segments.first().unwrap();
            let seg_ident = &seg.ident;
            let seg_ident_string = seg.ident.to_string();
            if !self.pubs.contains(&seg_ident_string) {
                if KNOWN_WEB_SYS_TYPES.contains(&seg_ident_string.as_str()) {
                    self.uses.insert(parse_quote! {
                        use ::web_sys:: #seg_ident;
                    });
                } else if KNOWN_JS_SYS_TYPES.contains(&seg_ident_string.as_str()) {
                    self.uses.insert(parse_quote! {
                        use ::js_sys:: #seg_ident;
                    });
                }
            }
        }
        for seg in &t.path.segments {
            self.visit_path_segment(seg);
        }
    }

    fn visit_attribute(&mut self, attr: &'ast Attribute) {
        if let Some(ExprPath { path, .. }) = extends(attr) {
            self.visit_type_path(&TypePath {
                qself: None,
                path: path.clone(),
            });
        }
    }
}

/// Make bindings adhere to WasmAbi traits
pub struct WasmAbify {
    pub wasm_abi_types: HashSet<Type>,
}

#[derive(Default, Debug)]
struct NestedTyFinder<'ast> {
    result: Option<&'ast Type>,
}

impl<'ast> Visit<'ast> for NestedTyFinder<'ast> {
    fn visit_type(&mut self, t: &'ast Type) {
        if let Type::Path(tp) = t {
            if tp.path.segments.len() == 3 {
                let seg = tp.path.segments.last().unwrap();
                if seg.ident == "Option" {
                    if let PathArguments::AngleBracketed(AngleBracketedGenericArguments {
                        args,
                        ..
                    }) = &seg.arguments
                    {
                        if args.len() == 1 {
                            if let GenericArgument::Type(t) = args.first().unwrap() {
                                self.visit_type(t)
                            }
                        }
                    }
                } else if seg.ident == "Box" {
                    if let PathArguments::AngleBracketed(AngleBracketedGenericArguments {
                        args,
                        ..
                    }) = &seg.arguments
                    {
                        if args.len() == 1 {
                            if let GenericArgument::Type(Type::Slice(TypeSlice { elem, .. })) =
                                args.first().unwrap()
                            {
                                self.visit_type(elem);
                            }
                        }
                    }
                }
            } else if tp.path.segments.len() == 1 {
                let seg = tp.path.segments.first().unwrap();
                if seg.arguments.is_empty() {
                    self.result = Some(t);
                }
            }
        } else {
            self.result = Some(t);
        }
    }
}

impl VisitMut for WasmAbify {
    fn visit_return_type_mut(&mut self, rt: &mut ReturnType) {
        // Can't return references
        if let ReturnType::Type(_, ty) = rt {
            let mut tyf = NestedTyFinder::default();
            tyf.visit_type(ty);
            if let Some(Type::Reference(TypeReference { elem, .. })) = tyf.result {
                if let Type::TraitObject(_) = elem.as_ref() {
                    *ty = Box::new(js_value().into());
                    return;
                }
            }
            self.visit_type_mut(ty);
        }
    }

    fn visit_type_mut(&mut self, t: &mut Type) {
        // Allow dyn Fns
        if let Type::Reference(TypeReference { elem, .. }) = t {
            if let Type::TraitObject(_) = elem.as_ref() {
                return;
            }
        }
        if !self.wasm_abi_types.contains(t) {
            *t = js_value().into();
        }
    }
}

lazy_static! {
    pub static ref KNOWN_STRING_TYPES: HashSet<&'static str> = [
        "AlignSetting",
        "AnimationPlayState",
        "AnimationReplaceState",
        "AppendMode",
        "AttestationConveyancePreference",
        "AudioContextLatencyCategory",
        "AudioContextState",
        "AuthenticatorAttachment",
        "AuthenticatorTransport",
        "AutoKeyword",
        "AutomationRate",
        "BinaryType",
        "BiquadFilterType",
        "CanPlayTypeResult",
        "CanvasDirection",
        "CanvasFillRule",
        "CanvasFontKerning",
        "CanvasFontStretch",
        "CanvasFontVariantCaps",
        "CanvasLineCap",
        "CanvasLineJoin",
        "CanvasTextAlign",
        "CanvasTextBaseline",
        "CanvasTextRendering",
        "ChannelCountMode",
        "ChannelInterpretation",
        "ClientTypes",
        "ColorGamut",
        "ColorSpaceConversion",
        "CompositeOperation",
        "CompositeOperationOrAuto",
        "CredentialMediationRequirement",
        "DOMParserSupportedType",
        "DirectionSetting",
        "DisplayCaptureSurfaceType",
        "DistanceModelType",
        "DocumentReadyState",
        "DocumentVisibilityState",
        "EndOfStreamError",
        "EndingType",
        "FileSystemHandleKind",
        "FillMode",
        "FontFaceLoadStatus",
        "FontFaceSetLoadStatus",
        "FullscreenNavigationUI",
        "GamepadHapticActuatorType",
        "GamepadMappingType",
        "GlobalCompositeOperation",
        "HdrMetadataType",
        "IDBCursorDirection",
        "IDBRequestReadyState",
        "IDBTransactionDurability",
        "IDBTransactionMode",
        "ImageOrientation",
        "ImageSmoothingQuality",
        "IterationCompositeOperation",
        "KeyFormat",
        "KeyType",
        "KeyUsage",
        "LineAlignSetting",
        "LockMode",
        "MediaDecodingType",
        "MediaDeviceKind",
        "MediaEncodingType",
        "MediaKeyMessageType",
        "MediaKeySessionClosedReason",
        "MediaKeySessionType",
        "MediaKeyStatus",
        "MediaKeysRequirement",
        "MediaSessionAction",
        "MediaSessionPlaybackState",
        "MediaStreamTrackState",
        "NavigationTimingType",
        "NotificationDirection",
        "NotificationPermission",
        "OrientationLockType",
        "OrientationType",
        "OscillatorType",
        "OverSampleType",
        "PanningModelType",
        "PaymentComplete",
        "PermissionName",
        "PermissionState",
        "PlaybackDirection",
        "PositionAlignSetting",
        "PredefinedColorSpace",
        "PremultiplyAlpha",
        "PresentationStyle",
        "PublicKeyCredentialType",
        "PushEncryptionKeyName",
        "RTCBundlePolicy",
        "RTCDataChannelState",
        "RTCDegradationPreference",
        "RTCDtlsTransportState",
        "RTCEncodedVideoFrameType",
        "RTCErrorDetailType",
        "RTCIceCandidateType",
        "RTCIceComponent",
        "RTCIceConnectionState",
        "RTCIceCredentialType",
        "RTCIceGathererState",
        "RTCIceGatheringState",
        "RTCIceProtocol",
        "RTCIceTcpCandidateType",
        "RTCIceTransportPolicy",
        "RTCIceTransportState",
        "RTCPeerConnectionState",
        "RTCPriorityType",
        "RTCRtcpMuxPolicy",
        "RTCRtpTransceiverDirection",
        "RTCSctpTransportState",
        "RTCSdpType",
        "RTCSignalingState",
        "RTCStatsIceCandidatePairState",
        "RTCStatsType",
        "ReadyState",
        "RecordingState",
        "ReferrerPolicy",
        "RemotePlaybackState",
        "RequestCache",
        "RequestCredentials",
        "RequestDestination",
        "RequestMode",
        "RequestRedirect",
        "ResidentKeyRequirement",
        "ResizeObserverBoxOptions",
        "ResizeQuality",
        "ResponseType",
        "ScrollBehavior",
        "ScrollLogicalPosition",
        "ScrollRestoration",
        "ScrollSetting",
        "SecurityPolicyViolationEventDisposition",
        "SelectionMode",
        "ServiceWorkerState",
        "ServiceWorkerUpdateViaCache",
        "ShadowRootMode",
        "SlotAssignmentMode",
        "SpeechSynthesisErrorCode",
        "TextTrackKind",
        "TextTrackMode",
        "TouchType",
        "TransferFunction",
        "UserVerificationRequirement",
        "VideoColorPrimaries",
        "VideoFacingModeEnum",
        "VideoMatrixCoefficients",
        "VideoTransferCharacteristics",
        "WebGLPowerPreference",
        "WorkerType",
        "XMLHttpRequestResponseType",
    ]
    .into_iter()
    .collect();
    pub static ref KNOWN_WEB_SYS_TYPES: HashSet<&'static str> = [
        "AbortController",
        "AbortSignal",
        "AddEventListenerOptions",
        "AesCbcParams",
        "AesCtrParams",
        "AesDerivedKeyParams",
        "AesGcmParams",
        "AesKeyAlgorithm",
        "AesKeyGenParams",
        "Algorithm",
        "AllowedBluetoothDevice",
        "AllowedUsbDevice",
        "AnalyserNode",
        "AnalyserOptions",
        "AngleInstancedArrays",
        "Animation",
        "AnimationEffect",
        "AnimationEvent",
        "AnimationEventInit",
        "AnimationPlaybackEvent",
        "AnimationPlaybackEventInit",
        "AnimationPropertyDetails",
        "AnimationPropertyValueDetails",
        "AnimationTimeline",
        "AssignedNodesOptions",
        "Attr",
        "AttributeNameValue",
        "AudioBuffer",
        "AudioBufferOptions",
        "AudioBufferSourceNode",
        "AudioBufferSourceOptions",
        "AudioConfiguration",
        "AudioContext",
        "AudioContextOptions",
        "AudioData",
        "AudioDataCopyToOptions",
        "AudioDataInit",
        "AudioDecoder",
        "AudioDecoderConfig",
        "AudioDecoderInit",
        "AudioDecoderSupport",
        "AudioDestinationNode",
        "AudioEncoder",
        "AudioEncoderConfig",
        "AudioEncoderInit",
        "AudioEncoderSupport",
        "AudioListener",
        "AudioNode",
        "AudioNodeOptions",
        "AudioParam",
        "AudioParamMap",
        "AudioProcessingEvent",
        "AudioScheduledSourceNode",
        "AudioStreamTrack",
        "AudioTrack",
        "AudioTrackList",
        "AudioWorklet",
        "AudioWorkletGlobalScope",
        "AudioWorkletNode",
        "AudioWorkletNodeOptions",
        "AudioWorkletProcessor",
        "AuthenticationExtensionsClientInputs",
        "AuthenticationExtensionsClientOutputs",
        "AuthenticatorAssertionResponse",
        "AuthenticatorAttestationResponse",
        "AuthenticatorResponse",
        "AuthenticatorSelectionCriteria",
        "AutocompleteInfo",
        "BarProp",
        "BaseAudioContext",
        "BaseComputedKeyframe",
        "BaseKeyframe",
        "BasePropertyIndexedKeyframe",
        "BasicCardRequest",
        "BasicCardResponse",
        "BatteryManager",
        "BeforeUnloadEvent",
        "BiquadFilterNode",
        "BiquadFilterOptions",
        "Blob",
        "BlobEvent",
        "BlobEventInit",
        "BlobPropertyBag",
        "BlockParsingOptions",
        "Bluetooth",
        "BluetoothAdvertisingEvent",
        "BluetoothAdvertisingEventInit",
        "BluetoothCharacteristicProperties",
        "BluetoothDataFilterInit",
        "BluetoothDevice",
        "BluetoothLeScanFilterInit",
        "BluetoothManufacturerDataMap",
        "BluetoothPermissionDescriptor",
        "BluetoothPermissionResult",
        "BluetoothPermissionStorage",
        "BluetoothRemoteGattCharacteristic",
        "BluetoothRemoteGattDescriptor",
        "BluetoothRemoteGattServer",
        "BluetoothRemoteGattService",
        "BluetoothServiceDataMap",
        "BluetoothUuid",
        "BoxQuadOptions",
        "BroadcastChannel",
        "BrowserElementDownloadOptions",
        "BrowserElementExecuteScriptOptions",
        "BrowserFeedWriter",
        "ByteLengthQueuingStrategy",
        "Cache",
        "CacheBatchOperation",
        "CacheQueryOptions",
        "CacheStorage",
        "CanvasCaptureMediaStream",
        "CanvasGradient",
        "CanvasPattern",
        "CanvasRenderingContext2d",
        "CaretPosition",
        "CaretStateChangedEventInit",
        "CdataSection",
        "ChannelMergerNode",
        "ChannelMergerOptions",
        "ChannelPixelLayout",
        "ChannelSplitterNode",
        "ChannelSplitterOptions",
        "CharacterData",
        "CheckerboardReport",
        "CheckerboardReportService",
        "ChromeFilePropertyBag",
        "ChromeWorker",
        "Client",
        "ClientQueryOptions",
        "ClientRectsAndTexts",
        "Clients",
        "Clipboard",
        "ClipboardEvent",
        "ClipboardEventInit",
        "ClipboardItem",
        "ClipboardItemOptions",
        "ClipboardPermissionDescriptor",
        "CloseEvent",
        "CloseEventInit",
        "CollectedClientData",
        "Comment",
        "CompositionEvent",
        "CompositionEventInit",
        "ComputedEffectTiming",
        "ConnStatusDict",
        "ConsoleCounter",
        "ConsoleCounterError",
        "ConsoleEvent",
        "ConsoleInstance",
        "ConsoleInstanceOptions",
        "ConsoleProfileEvent",
        "ConsoleStackEntry",
        "ConsoleTimerError",
        "ConsoleTimerLogOrEnd",
        "ConsoleTimerStart",
        "ConstantSourceNode",
        "ConstantSourceOptions",
        "ConstrainBooleanParameters",
        "ConstrainDomStringParameters",
        "ConstrainDoubleRange",
        "ConstrainLongRange",
        "ContextAttributes2d",
        "ConvertCoordinateOptions",
        "ConvolverNode",
        "ConvolverOptions",
        "Coordinates",
        "CountQueuingStrategy",
        "Credential",
        "CredentialCreationOptions",
        "CredentialRequestOptions",
        "CredentialsContainer",
        "Crypto",
        "CryptoKey",
        "CryptoKeyPair",
        "Csp",
        "CspPolicies",
        "CspReport",
        "CspReportProperties",
        "CssAnimation",
        "CssConditionRule",
        "CssCounterStyleRule",
        "CssFontFaceRule",
        "CssFontFeatureValuesRule",
        "CssGroupingRule",
        "CssImportRule",
        "CssKeyframeRule",
        "CssKeyframesRule",
        "CssMediaRule",
        "CssNamespaceRule",
        "CssPageRule",
        "CssPseudoElement",
        "CssRule",
        "CssRuleList",
        "CssStyleDeclaration",
        "CssStyleRule",
        "CssStyleSheet",
        "CssSupportsRule",
        "CssTransition",
        "CustomElementRegistry",
        "CustomEvent",
        "CustomEventInit",
        "DataTransfer",
        "DataTransferItem",
        "DataTransferItemList",
        "DateTimeValue",
        "DecoderDoctorNotification",
        "DedicatedWorkerGlobalScope",
        "DelayNode",
        "DelayOptions",
        "DeviceAcceleration",
        "DeviceAccelerationInit",
        "DeviceLightEvent",
        "DeviceLightEventInit",
        "DeviceMotionEvent",
        "DeviceMotionEventInit",
        "DeviceOrientationEvent",
        "DeviceOrientationEventInit",
        "DeviceProximityEvent",
        "DeviceProximityEventInit",
        "DeviceRotationRate",
        "DeviceRotationRateInit",
        "DhKeyDeriveParams",
        "Directory",
        "DisplayMediaStreamConstraints",
        "DisplayNameOptions",
        "DisplayNameResult",
        "DnsCacheDict",
        "DnsCacheEntry",
        "DnsLookupDict",
        "Document",
        "DocumentFragment",
        "DocumentTimeline",
        "DocumentTimelineOptions",
        "DocumentType",
        "DomError",
        "DomException",
        "DomImplementation",
        "DomMatrix",
        "DomMatrixReadOnly",
        "DomParser",
        "DomPoint",
        "DomPointInit",
        "DomPointReadOnly",
        "DomQuad",
        "DomQuadInit",
        "DomQuadJson",
        "DomRect",
        "DomRectInit",
        "DomRectList",
        "DomRectReadOnly",
        "DomRequest",
        "DomStringList",
        "DomStringMap",
        "DomTokenList",
        "DomWindowResizeEventDetail",
        "DragEvent",
        "DragEventInit",
        "DynamicsCompressorNode",
        "DynamicsCompressorOptions",
        "EcKeyAlgorithm",
        "EcKeyGenParams",
        "EcKeyImportParams",
        "EcdhKeyDeriveParams",
        "EcdsaParams",
        "EffectTiming",
        "Element",
        "ElementCreationOptions",
        "ElementDefinitionOptions",
        "EncodedAudioChunk",
        "EncodedAudioChunkInit",
        "EncodedAudioChunkMetadata",
        "EncodedVideoChunk",
        "EncodedVideoChunkInit",
        "EncodedVideoChunkMetadata",
        "ErrorCallback",
        "ErrorEvent",
        "ErrorEventInit",
        "Event",
        "EventInit",
        "EventListener",
        "EventListenerOptions",
        "EventModifierInit",
        "EventSource",
        "EventSourceInit",
        "EventTarget",
        "Exception",
        "ExtBlendMinmax",
        "ExtColorBufferFloat",
        "ExtColorBufferHalfFloat",
        "ExtDisjointTimerQuery",
        "ExtFragDepth",
        "ExtSRgb",
        "ExtShaderTextureLod",
        "ExtTextureFilterAnisotropic",
        "ExtendableEvent",
        "ExtendableEventInit",
        "ExtendableMessageEvent",
        "ExtendableMessageEventInit",
        "External",
        "FakePluginMimeEntry",
        "FakePluginTagInit",
        "FetchEvent",
        "FetchEventInit",
        "FetchObserver",
        "FetchReadableStreamReadDataArray",
        "FetchReadableStreamReadDataDone",
        "File",
        "FileCallback",
        "FileList",
        "FilePropertyBag",
        "FileReader",
        "FileReaderSync",
        "FileSystem",
        "FileSystemDirectoryEntry",
        "FileSystemDirectoryReader",
        "FileSystemEntriesCallback",
        "FileSystemEntry",
        "FileSystemEntryCallback",
        "FileSystemFileEntry",
        "FileSystemFlags",
        "FocusEvent",
        "FocusEventInit",
        "FontFace",
        "FontFaceDescriptors",
        "FontFaceSet",
        "FontFaceSetIterator",
        "FontFaceSetIteratorResult",
        "FontFaceSetLoadEvent",
        "FontFaceSetLoadEventInit",
        "FormData",
        "FuzzingFunctions",
        "GainNode",
        "GainOptions",
        "Gamepad",
        "GamepadAxisMoveEvent",
        "GamepadAxisMoveEventInit",
        "GamepadButton",
        "GamepadButtonEvent",
        "GamepadButtonEventInit",
        "GamepadEvent",
        "GamepadEventInit",
        "GamepadHapticActuator",
        "GamepadPose",
        "GamepadServiceTest",
        "Geolocation",
        "GetNotificationOptions",
        "GetRootNodeOptions",
        "GetUserMediaRequest",
        "Gpu",
        "GpuAdapter",
        "GpuAdapterInfo",
        "GpuBindGroup",
        "GpuBindGroupDescriptor",
        "GpuBindGroupEntry",
        "GpuBindGroupLayout",
        "GpuBindGroupLayoutDescriptor",
        "GpuBindGroupLayoutEntry",
        "GpuBlendComponent",
        "GpuBlendState",
        "GpuBuffer",
        "GpuBufferBinding",
        "GpuBufferBindingLayout",
        "GpuBufferDescriptor",
        "GpuCanvasConfiguration",
        "GpuCanvasContext",
        "GpuColorDict",
        "GpuColorTargetState",
        "GpuCommandBuffer",
        "GpuCommandBufferDescriptor",
        "GpuCommandEncoder",
        "GpuCommandEncoderDescriptor",
        "GpuCompilationInfo",
        "GpuCompilationMessage",
        "GpuComputePassDescriptor",
        "GpuComputePassEncoder",
        "GpuComputePassTimestampWrite",
        "GpuComputePipeline",
        "GpuComputePipelineDescriptor",
        "GpuDepthStencilState",
        "GpuDevice",
        "GpuDeviceDescriptor",
        "GpuDeviceLostInfo",
        "GpuError",
        "GpuExtent3dDict",
        "GpuExternalTexture",
        "GpuExternalTextureBindingLayout",
        "GpuExternalTextureDescriptor",
        "GpuFragmentState",
        "GpuImageCopyBuffer",
        "GpuImageCopyExternalImage",
        "GpuImageCopyTexture",
        "GpuImageCopyTextureTagged",
        "GpuImageDataLayout",
        "GpuMultisampleState",
        "GpuObjectDescriptorBase",
        "GpuOrigin2dDict",
        "GpuOrigin3dDict",
        "GpuOutOfMemoryError",
        "GpuPipelineDescriptorBase",
        "GpuPipelineLayout",
        "GpuPipelineLayoutDescriptor",
        "GpuPrimitiveState",
        "GpuProgrammableStage",
        "GpuQuerySet",
        "GpuQuerySetDescriptor",
        "GpuQueue",
        "GpuQueueDescriptor",
        "GpuRenderBundle",
        "GpuRenderBundleDescriptor",
        "GpuRenderBundleEncoder",
        "GpuRenderBundleEncoderDescriptor",
        "GpuRenderPassColorAttachment",
        "GpuRenderPassDepthStencilAttachment",
        "GpuRenderPassDescriptor",
        "GpuRenderPassEncoder",
        "GpuRenderPassLayout",
        "GpuRenderPassTimestampWrite",
        "GpuRenderPipeline",
        "GpuRenderPipelineDescriptor",
        "GpuRequestAdapterOptions",
        "GpuSampler",
        "GpuSamplerBindingLayout",
        "GpuSamplerDescriptor",
        "GpuShaderModule",
        "GpuShaderModuleCompilationHint",
        "GpuShaderModuleDescriptor",
        "GpuStencilFaceState",
        "GpuStorageTextureBindingLayout",
        "GpuSupportedFeatures",
        "GpuSupportedLimits",
        "GpuTexture",
        "GpuTextureBindingLayout",
        "GpuTextureDescriptor",
        "GpuTextureView",
        "GpuTextureViewDescriptor",
        "GpuUncapturedErrorEvent",
        "GpuUncapturedErrorEventInit",
        "GpuValidationError",
        "GpuVertexAttribute",
        "GpuVertexBufferLayout",
        "GpuVertexState",
        "GroupedHistoryEventInit",
        "HalfOpenInfoDict",
        "HashChangeEvent",
        "HashChangeEventInit",
        "Headers",
        "Hid",
        "HidCollectionInfo",
        "HidConnectionEvent",
        "HidConnectionEventInit",
        "HidDevice",
        "HidDeviceFilter",
        "HidDeviceRequestOptions",
        "HidInputReportEvent",
        "HidInputReportEventInit",
        "HidReportInfo",
        "HidReportItem",
        "HiddenPluginEventInit",
        "History",
        "HitRegionOptions",
        "HkdfParams",
        "HmacDerivedKeyParams",
        "HmacImportParams",
        "HmacKeyAlgorithm",
        "HmacKeyGenParams",
        "HtmlAllCollection",
        "HtmlAnchorElement",
        "HtmlAreaElement",
        "HtmlAudioElement",
        "HtmlBaseElement",
        "HtmlBodyElement",
        "HtmlBrElement",
        "HtmlButtonElement",
        "HtmlCanvasElement",
        "HtmlCollection",
        "HtmlDListElement",
        "HtmlDataElement",
        "HtmlDataListElement",
        "HtmlDetailsElement",
        "HtmlDialogElement",
        "HtmlDirectoryElement",
        "HtmlDivElement",
        "HtmlDocument",
        "HtmlElement",
        "HtmlEmbedElement",
        "HtmlFieldSetElement",
        "HtmlFontElement",
        "HtmlFormControlsCollection",
        "HtmlFormElement",
        "HtmlFrameElement",
        "HtmlFrameSetElement",
        "HtmlHeadElement",
        "HtmlHeadingElement",
        "HtmlHrElement",
        "HtmlHtmlElement",
        "HtmlIFrameElement",
        "HtmlImageElement",
        "HtmlInputElement",
        "HtmlLabelElement",
        "HtmlLegendElement",
        "HtmlLiElement",
        "HtmlLinkElement",
        "HtmlMapElement",
        "HtmlMediaElement",
        "HtmlMenuElement",
        "HtmlMenuItemElement",
        "HtmlMetaElement",
        "HtmlMeterElement",
        "HtmlModElement",
        "HtmlOListElement",
        "HtmlObjectElement",
        "HtmlOptGroupElement",
        "HtmlOptionElement",
        "HtmlOptionsCollection",
        "HtmlOutputElement",
        "HtmlParagraphElement",
        "HtmlParamElement",
        "HtmlPictureElement",
        "HtmlPreElement",
        "HtmlProgressElement",
        "HtmlQuoteElement",
        "HtmlScriptElement",
        "HtmlSelectElement",
        "HtmlSlotElement",
        "HtmlSourceElement",
        "HtmlSpanElement",
        "HtmlStyleElement",
        "HtmlTableCaptionElement",
        "HtmlTableCellElement",
        "HtmlTableColElement",
        "HtmlTableElement",
        "HtmlTableRowElement",
        "HtmlTableSectionElement",
        "HtmlTemplateElement",
        "HtmlTextAreaElement",
        "HtmlTimeElement",
        "HtmlTitleElement",
        "HtmlTrackElement",
        "HtmlUListElement",
        "HtmlUnknownElement",
        "HtmlVideoElement",
        "HttpConnDict",
        "HttpConnInfo",
        "HttpConnectionElement",
        "IdbCursor",
        "IdbCursorWithValue",
        "IdbDatabase",
        "IdbFactory",
        "IdbFileHandle",
        "IdbFileMetadataParameters",
        "IdbFileRequest",
        "IdbIndex",
        "IdbIndexParameters",
        "IdbKeyRange",
        "IdbLocaleAwareKeyRange",
        "IdbMutableFile",
        "IdbObjectStore",
        "IdbObjectStoreParameters",
        "IdbOpenDbOptions",
        "IdbOpenDbRequest",
        "IdbRequest",
        "IdbTransaction",
        "IdbVersionChangeEvent",
        "IdbVersionChangeEventInit",
        "IdleDeadline",
        "IdleRequestOptions",
        "IirFilterNode",
        "IirFilterOptions",
        "ImageBitmap",
        "ImageBitmapRenderingContext",
        "ImageCapture",
        "ImageCaptureError",
        "ImageCaptureErrorEvent",
        "ImageCaptureErrorEventInit",
        "ImageData",
        "ImageDecodeOptions",
        "ImageDecodeResult",
        "ImageDecoder",
        "ImageDecoderInit",
        "ImageTrack",
        "ImageTrackList",
        "InputEvent",
        "InputEventInit",
        "InstallTriggerData",
        "IntersectionObserver",
        "IntersectionObserverEntry",
        "IntersectionObserverEntryInit",
        "IntersectionObserverInit",
        "IntlUtils",
        "IterableKeyAndValueResult",
        "IterableKeyOrValueResult",
        "JsonWebKey",
        "KeyAlgorithm",
        "KeyEvent",
        "KeyIdsInitData",
        "KeyboardEvent",
        "KeyboardEventInit",
        "KeyframeEffect",
        "KeyframeEffectOptions",
        "L10nElement",
        "L10nValue",
        "LifecycleCallbacks",
        "ListBoxObject",
        "LocalMediaStream",
        "LocaleInfo",
        "Location",
        "MediaCapabilities",
        "MediaCapabilitiesInfo",
        "MediaConfiguration",
        "MediaDecodingConfiguration",
        "MediaDeviceInfo",
        "MediaDevices",
        "MediaElementAudioSourceNode",
        "MediaElementAudioSourceOptions",
        "MediaEncodingConfiguration",
        "MediaEncryptedEvent",
        "MediaError",
        "MediaImage",
        "MediaKeyError",
        "MediaKeyMessageEvent",
        "MediaKeyMessageEventInit",
        "MediaKeyNeededEventInit",
        "MediaKeySession",
        "MediaKeyStatusMap",
        "MediaKeySystemAccess",
        "MediaKeySystemConfiguration",
        "MediaKeySystemMediaCapability",
        "MediaKeys",
        "MediaKeysPolicy",
        "MediaList",
        "MediaMetadata",
        "MediaMetadataInit",
        "MediaPositionState",
        "MediaQueryList",
        "MediaQueryListEvent",
        "MediaQueryListEventInit",
        "MediaRecorder",
        "MediaRecorderErrorEvent",
        "MediaRecorderErrorEventInit",
        "MediaRecorderOptions",
        "MediaSession",
        "MediaSessionActionDetails",
        "MediaSource",
        "MediaStream",
        "MediaStreamAudioDestinationNode",
        "MediaStreamAudioSourceNode",
        "MediaStreamAudioSourceOptions",
        "MediaStreamConstraints",
        "MediaStreamError",
        "MediaStreamEvent",
        "MediaStreamEventInit",
        "MediaStreamTrack",
        "MediaStreamTrackEvent",
        "MediaStreamTrackEventInit",
        "MediaStreamTrackGenerator",
        "MediaStreamTrackGeneratorInit",
        "MediaStreamTrackProcessor",
        "MediaStreamTrackProcessorInit",
        "MediaTrackConstraintSet",
        "MediaTrackConstraints",
        "MediaTrackSettings",
        "MediaTrackSupportedConstraints",
        "MessageChannel",
        "MessageEvent",
        "MessageEventInit",
        "MessagePort",
        "MidiAccess",
        "MidiConnectionEvent",
        "MidiConnectionEventInit",
        "MidiInput",
        "MidiInputMap",
        "MidiMessageEvent",
        "MidiMessageEventInit",
        "MidiOptions",
        "MidiOutput",
        "MidiOutputMap",
        "MidiPort",
        "MimeType",
        "MimeTypeArray",
        "MouseEvent",
        "MouseEventInit",
        "MouseScrollEvent",
        "MozDebug",
        "MutationEvent",
        "MutationObserver",
        "MutationObserverInit",
        "MutationObservingInfo",
        "MutationRecord",
        "NamedNodeMap",
        "NativeOsFileReadOptions",
        "NativeOsFileWriteAtomicOptions",
        "Navigator",
        "NavigatorAutomationInformation",
        "NetworkCommandOptions",
        "NetworkInformation",
        "NetworkResultOptions",
        "Node",
        "NodeFilter",
        "NodeIterator",
        "NodeList",
        "Notification",
        "NotificationBehavior",
        "NotificationEvent",
        "NotificationEventInit",
        "NotificationOptions",
        "ObserverCallback",
        "OesElementIndexUint",
        "OesStandardDerivatives",
        "OesTextureFloat",
        "OesTextureFloatLinear",
        "OesTextureHalfFloat",
        "OesTextureHalfFloatLinear",
        "OesVertexArrayObject",
        "OfflineAudioCompletionEvent",
        "OfflineAudioCompletionEventInit",
        "OfflineAudioContext",
        "OfflineAudioContextOptions",
        "OfflineResourceList",
        "OffscreenCanvas",
        "OpenWindowEventDetail",
        "OptionalEffectTiming",
        "OscillatorNode",
        "OscillatorOptions",
        "OvrMultiview2",
        "PageTransitionEvent",
        "PageTransitionEventInit",
        "PaintRequest",
        "PaintRequestList",
        "PaintWorkletGlobalScope",
        "PannerNode",
        "PannerOptions",
        "Path2d",
        "PaymentAddress",
        "PaymentMethodChangeEvent",
        "PaymentMethodChangeEventInit",
        "PaymentRequestUpdateEvent",
        "PaymentRequestUpdateEventInit",
        "PaymentResponse",
        "Pbkdf2Params",
        "Performance",
        "PerformanceEntry",
        "PerformanceEntryEventInit",
        "PerformanceEntryFilterOptions",
        "PerformanceMark",
        "PerformanceMeasure",
        "PerformanceNavigation",
        "PerformanceNavigationTiming",
        "PerformanceObserver",
        "PerformanceObserverEntryList",
        "PerformanceObserverInit",
        "PerformanceResourceTiming",
        "PerformanceServerTiming",
        "PerformanceTiming",
        "PeriodicWave",
        "PeriodicWaveConstraints",
        "PeriodicWaveOptions",
        "PermissionDescriptor",
        "PermissionStatus",
        "Permissions",
        "PlaneLayout",
        "Plugin",
        "PluginArray",
        "PluginCrashedEventInit",
        "PointerEvent",
        "PointerEventInit",
        "PopStateEvent",
        "PopStateEventInit",
        "PopupBlockedEvent",
        "PopupBlockedEventInit",
        "Position",
        "PositionError",
        "PositionOptions",
        "Presentation",
        "PresentationAvailability",
        "PresentationConnection",
        "PresentationConnectionAvailableEvent",
        "PresentationConnectionAvailableEventInit",
        "PresentationConnectionCloseEvent",
        "PresentationConnectionCloseEventInit",
        "PresentationConnectionList",
        "PresentationReceiver",
        "PresentationRequest",
        "ProcessingInstruction",
        "ProfileTimelineLayerRect",
        "ProfileTimelineMarker",
        "ProfileTimelineStackFrame",
        "ProgressEvent",
        "ProgressEventInit",
        "PromiseNativeHandler",
        "PromiseRejectionEvent",
        "PromiseRejectionEventInit",
        "PublicKeyCredential",
        "PublicKeyCredentialCreationOptions",
        "PublicKeyCredentialDescriptor",
        "PublicKeyCredentialEntity",
        "PublicKeyCredentialParameters",
        "PublicKeyCredentialRequestOptions",
        "PublicKeyCredentialRpEntity",
        "PublicKeyCredentialUserEntity",
        "PushEvent",
        "PushEventInit",
        "PushManager",
        "PushMessageData",
        "PushSubscription",
        "PushSubscriptionInit",
        "PushSubscriptionJson",
        "PushSubscriptionKeys",
        "PushSubscriptionOptions",
        "PushSubscriptionOptionsInit",
        "QueuingStrategy",
        "QueuingStrategyInit",
        "RadioNodeList",
        "Range",
        "RcwnPerfStats",
        "RcwnStatus",
        "ReadableByteStreamController",
        "ReadableStream",
        "ReadableStreamByobReader",
        "ReadableStreamByobRequest",
        "ReadableStreamDefaultController",
        "ReadableStreamDefaultReader",
        "ReadableStreamGetReaderOptions",
        "ReadableStreamIteratorOptions",
        "ReadableStreamReadResult",
        "ReadableWritablePair",
        "RegisterRequest",
        "RegisterResponse",
        "RegisteredKey",
        "RegistrationOptions",
        "Request",
        "RequestDeviceOptions",
        "RequestInit",
        "RequestMediaKeySystemAccessNotification",
        "ResizeObserver",
        "ResizeObserverEntry",
        "ResizeObserverOptions",
        "ResizeObserverSize",
        "Response",
        "ResponseInit",
        "RsaHashedImportParams",
        "RsaOaepParams",
        "RsaOtherPrimesInfo",
        "RsaPssParams",
        "RtcAnswerOptions",
        "RtcCertificate",
        "RtcCertificateExpiration",
        "RtcCodecStats",
        "RtcConfiguration",
        "RtcDataChannel",
        "RtcDataChannelEvent",
        "RtcDataChannelEventInit",
        "RtcDataChannelInit",
        "RtcFecParameters",
        "RtcIceCandidate",
        "RtcIceCandidateInit",
        "RtcIceCandidatePairStats",
        "RtcIceCandidateStats",
        "RtcIceComponentStats",
        "RtcIceServer",
        "RtcIdentityAssertion",
        "RtcIdentityAssertionResult",
        "RtcIdentityProvider",
        "RtcIdentityProviderDetails",
        "RtcIdentityProviderOptions",
        "RtcIdentityProviderRegistrar",
        "RtcIdentityValidationResult",
        "RtcInboundRtpStreamStats",
        "RtcMediaStreamStats",
        "RtcMediaStreamTrackStats",
        "RtcOfferAnswerOptions",
        "RtcOfferOptions",
        "RtcOutboundRtpStreamStats",
        "RtcPeerConnection",
        "RtcPeerConnectionIceEvent",
        "RtcPeerConnectionIceEventInit",
        "RtcRtcpParameters",
        "RtcRtpCodecParameters",
        "RtcRtpContributingSource",
        "RtcRtpEncodingParameters",
        "RtcRtpHeaderExtensionParameters",
        "RtcRtpParameters",
        "RtcRtpReceiver",
        "RtcRtpSender",
        "RtcRtpSourceEntry",
        "RtcRtpSynchronizationSource",
        "RtcRtpTransceiver",
        "RtcRtpTransceiverInit",
        "RtcRtxParameters",
        "RtcSessionDescription",
        "RtcSessionDescriptionInit",
        "RtcStats",
        "RtcStatsReport",
        "RtcStatsReportInternal",
        "RtcTrackEvent",
        "RtcTrackEventInit",
        "RtcTransportStats",
        "RtcdtmfSender",
        "RtcdtmfToneChangeEvent",
        "RtcdtmfToneChangeEventInit",
        "RtcrtpContributingSourceStats",
        "RtcrtpStreamStats",
        "Screen",
        "ScreenLuminance",
        "ScreenOrientation",
        "ScriptProcessorNode",
        "ScrollAreaEvent",
        "ScrollBoxObject",
        "ScrollIntoViewOptions",
        "ScrollOptions",
        "ScrollToOptions",
        "ScrollViewChangeEventInit",
        "SecurityPolicyViolationEvent",
        "SecurityPolicyViolationEventInit",
        "Selection",
        "ServerSocketOptions",
        "ServiceWorker",
        "ServiceWorkerContainer",
        "ServiceWorkerGlobalScope",
        "ServiceWorkerRegistration",
        "ShadowRoot",
        "ShadowRootInit",
        "ShareData",
        "SharedWorker",
        "SharedWorkerGlobalScope",
        "SignResponse",
        "SocketElement",
        "SocketOptions",
        "SocketsDict",
        "SourceBuffer",
        "SourceBufferList",
        "SpeechGrammar",
        "SpeechGrammarList",
        "SpeechRecognition",
        "SpeechRecognitionAlternative",
        "SpeechRecognitionError",
        "SpeechRecognitionErrorInit",
        "SpeechRecognitionEvent",
        "SpeechRecognitionEventInit",
        "SpeechRecognitionResult",
        "SpeechRecognitionResultList",
        "SpeechSynthesis",
        "SpeechSynthesisErrorEvent",
        "SpeechSynthesisErrorEventInit",
        "SpeechSynthesisEvent",
        "SpeechSynthesisEventInit",
        "SpeechSynthesisUtterance",
        "SpeechSynthesisVoice",
        "StereoPannerNode",
        "StereoPannerOptions",
        "Storage",
        "StorageEstimate",
        "StorageEvent",
        "StorageEventInit",
        "StorageManager",
        "StreamPipeOptions",
        "StyleRuleChangeEventInit",
        "StyleSheet",
        "StyleSheetApplicableStateChangeEventInit",
        "StyleSheetChangeEventInit",
        "StyleSheetList",
        "SubmitEvent",
        "SubmitEventInit",
        "SubtleCrypto",
        "SvcOutputMetadata",
        "SvgAngle",
        "SvgAnimateElement",
        "SvgAnimateMotionElement",
        "SvgAnimateTransformElement",
        "SvgAnimatedAngle",
        "SvgAnimatedBoolean",
        "SvgAnimatedEnumeration",
        "SvgAnimatedInteger",
        "SvgAnimatedLength",
        "SvgAnimatedLengthList",
        "SvgAnimatedNumber",
        "SvgAnimatedNumberList",
        "SvgAnimatedPreserveAspectRatio",
        "SvgAnimatedRect",
        "SvgAnimatedString",
        "SvgAnimatedTransformList",
        "SvgAnimationElement",
        "SvgBoundingBoxOptions",
        "SvgCircleElement",
        "SvgClipPathElement",
        "SvgComponentTransferFunctionElement",
        "SvgDefsElement",
        "SvgDescElement",
        "SvgElement",
        "SvgEllipseElement",
        "SvgFilterElement",
        "SvgForeignObjectElement",
        "SvgGeometryElement",
        "SvgGradientElement",
        "SvgGraphicsElement",
        "SvgImageElement",
        "SvgLength",
        "SvgLengthList",
        "SvgLineElement",
        "SvgLinearGradientElement",
        "SvgMarkerElement",
        "SvgMaskElement",
        "SvgMatrix",
        "SvgMetadataElement",
        "SvgNumber",
        "SvgNumberList",
        "SvgPathElement",
        "SvgPathSeg",
        "SvgPathSegArcAbs",
        "SvgPathSegArcRel",
        "SvgPathSegClosePath",
        "SvgPathSegCurvetoCubicAbs",
        "SvgPathSegCurvetoCubicRel",
        "SvgPathSegCurvetoCubicSmoothAbs",
        "SvgPathSegCurvetoCubicSmoothRel",
        "SvgPathSegCurvetoQuadraticAbs",
        "SvgPathSegCurvetoQuadraticRel",
        "SvgPathSegCurvetoQuadraticSmoothAbs",
        "SvgPathSegCurvetoQuadraticSmoothRel",
        "SvgPathSegLinetoAbs",
        "SvgPathSegLinetoHorizontalAbs",
        "SvgPathSegLinetoHorizontalRel",
        "SvgPathSegLinetoRel",
        "SvgPathSegLinetoVerticalAbs",
        "SvgPathSegLinetoVerticalRel",
        "SvgPathSegList",
        "SvgPathSegMovetoAbs",
        "SvgPathSegMovetoRel",
        "SvgPatternElement",
        "SvgPoint",
        "SvgPointList",
        "SvgPolygonElement",
        "SvgPolylineElement",
        "SvgPreserveAspectRatio",
        "SvgRadialGradientElement",
        "SvgRect",
        "SvgRectElement",
        "SvgScriptElement",
        "SvgSetElement",
        "SvgStopElement",
        "SvgStringList",
        "SvgStyleElement",
        "SvgSwitchElement",
        "SvgSymbolElement",
        "SvgTextContentElement",
        "SvgTextElement",
        "SvgTextPathElement",
        "SvgTextPositioningElement",
        "SvgTitleElement",
        "SvgTransform",
        "SvgTransformList",
        "SvgUnitTypes",
        "SvgUseElement",
        "SvgViewElement",
        "SvgZoomAndPan",
        "SvgaElement",
        "SvgfeBlendElement",
        "SvgfeColorMatrixElement",
        "SvgfeComponentTransferElement",
        "SvgfeCompositeElement",
        "SvgfeConvolveMatrixElement",
        "SvgfeDiffuseLightingElement",
        "SvgfeDisplacementMapElement",
        "SvgfeDistantLightElement",
        "SvgfeDropShadowElement",
        "SvgfeFloodElement",
        "SvgfeFuncAElement",
        "SvgfeFuncBElement",
        "SvgfeFuncGElement",
        "SvgfeFuncRElement",
        "SvgfeGaussianBlurElement",
        "SvgfeImageElement",
        "SvgfeMergeElement",
        "SvgfeMergeNodeElement",
        "SvgfeMorphologyElement",
        "SvgfeOffsetElement",
        "SvgfePointLightElement",
        "SvgfeSpecularLightingElement",
        "SvgfeSpotLightElement",
        "SvgfeTileElement",
        "SvgfeTurbulenceElement",
        "SvggElement",
        "SvgmPathElement",
        "SvgsvgElement",
        "SvgtSpanElement",
        "TcpServerSocket",
        "TcpServerSocketEvent",
        "TcpServerSocketEventInit",
        "TcpSocket",
        "TcpSocketErrorEvent",
        "TcpSocketErrorEventInit",
        "TcpSocketEvent",
        "TcpSocketEventInit",
        "Text",
        "TextDecodeOptions",
        "TextDecoder",
        "TextDecoderOptions",
        "TextEncoder",
        "TextMetrics",
        "TextTrack",
        "TextTrackCue",
        "TextTrackCueList",
        "TextTrackList",
        "TimeEvent",
        "TimeRanges",
        "Touch",
        "TouchEvent",
        "TouchEventInit",
        "TouchInit",
        "TouchList",
        "TrackEvent",
        "TrackEventInit",
        "TransformStream",
        "TransformStreamDefaultController",
        "Transformer",
        "TransitionEvent",
        "TransitionEventInit",
        "TreeBoxObject",
        "TreeCellInfo",
        "TreeView",
        "TreeWalker",
        "U2f",
        "U2fClientData",
        "UdpMessageEventInit",
        "UdpOptions",
        "UiEvent",
        "UiEventInit",
        "UnderlyingSink",
        "UnderlyingSource",
        "Url",
        "UrlSearchParams",
        "Usb",
        "UsbAlternateInterface",
        "UsbConfiguration",
        "UsbConnectionEvent",
        "UsbConnectionEventInit",
        "UsbControlTransferParameters",
        "UsbDevice",
        "UsbDeviceFilter",
        "UsbDeviceRequestOptions",
        "UsbEndpoint",
        "UsbInTransferResult",
        "UsbInterface",
        "UsbIsochronousInTransferPacket",
        "UsbIsochronousInTransferResult",
        "UsbIsochronousOutTransferPacket",
        "UsbIsochronousOutTransferResult",
        "UsbOutTransferResult",
        "UsbPermissionDescriptor",
        "UsbPermissionResult",
        "UsbPermissionStorage",
        "UserProximityEvent",
        "UserProximityEventInit",
        "ValidityState",
        "ValueEvent",
        "ValueEventInit",
        "VideoColorSpace",
        "VideoColorSpaceInit",
        "VideoConfiguration",
        "VideoDecoder",
        "VideoDecoderConfig",
        "VideoDecoderInit",
        "VideoDecoderSupport",
        "VideoEncoder",
        "VideoEncoderConfig",
        "VideoEncoderEncodeOptions",
        "VideoEncoderInit",
        "VideoEncoderSupport",
        "VideoFrame",
        "VideoFrameBufferInit",
        "VideoFrameCopyToOptions",
        "VideoFrameInit",
        "VideoPlaybackQuality",
        "VideoStreamTrack",
        "VideoTrack",
        "VideoTrackList",
        "VoidCallback",
        "VrDisplay",
        "VrDisplayCapabilities",
        "VrEyeParameters",
        "VrFieldOfView",
        "VrFrameData",
        "VrLayer",
        "VrMockController",
        "VrMockDisplay",
        "VrPose",
        "VrServiceTest",
        "VrStageParameters",
        "VrSubmitFrameResult",
        "VttCue",
        "VttRegion",
        "WakeLock",
        "WakeLockSentinel",
        "WatchAdvertisementsOptions",
        "WaveShaperNode",
        "WaveShaperOptions",
        "WebGl2RenderingContext",
        "WebGlActiveInfo",
        "WebGlBuffer",
        "WebGlContextAttributes",
        "WebGlContextEvent",
        "WebGlContextEventInit",
        "WebGlFramebuffer",
        "WebGlProgram",
        "WebGlQuery",
        "WebGlRenderbuffer",
        "WebGlRenderingContext",
        "WebGlSampler",
        "WebGlShader",
        "WebGlShaderPrecisionFormat",
        "WebGlSync",
        "WebGlTexture",
        "WebGlTransformFeedback",
        "WebGlUniformLocation",
        "WebGlVertexArrayObject",
        "WebKitCssMatrix",
        "WebSocket",
        "WebSocketDict",
        "WebSocketElement",
        "WebglColorBufferFloat",
        "WebglCompressedTextureAstc",
        "WebglCompressedTextureAtc",
        "WebglCompressedTextureEtc",
        "WebglCompressedTextureEtc1",
        "WebglCompressedTexturePvrtc",
        "WebglCompressedTextureS3tc",
        "WebglCompressedTextureS3tcSrgb",
        "WebglDebugRendererInfo",
        "WebglDebugShaders",
        "WebglDepthTexture",
        "WebglDrawBuffers",
        "WebglLoseContext",
        "WebglMultiDraw",
        "WebrtcGlobalStatisticsReport",
        "WheelEvent",
        "WheelEventInit",
        "WidevineCdmManifest",
        "Window",
        "WindowClient",
        "Worker",
        "WorkerDebuggerGlobalScope",
        "WorkerGlobalScope",
        "WorkerLocation",
        "WorkerNavigator",
        "WorkerOptions",
        "Worklet",
        "WorkletGlobalScope",
        "WorkletOptions",
        "WritableStream",
        "WritableStreamDefaultController",
        "WritableStreamDefaultWriter",
        "XPathExpression",
        "XPathNsResolver",
        "XPathResult",
        "XmlDocument",
        "XmlHttpRequest",
        "XmlHttpRequestEventTarget",
        "XmlHttpRequestUpload",
        "XmlSerializer",
        "XrBoundedReferenceSpace",
        "XrFrame",
        "XrInputSource",
        "XrInputSourceArray",
        "XrInputSourceEvent",
        "XrInputSourceEventInit",
        "XrInputSourcesChangeEvent",
        "XrInputSourcesChangeEventInit",
        "XrLayer",
        "XrPermissionDescriptor",
        "XrPermissionStatus",
        "XrPose",
        "XrReferenceSpace",
        "XrReferenceSpaceEvent",
        "XrReferenceSpaceEventInit",
        "XrRenderState",
        "XrRenderStateInit",
        "XrRigidTransform",
        "XrSession",
        "XrSessionEvent",
        "XrSessionEventInit",
        "XrSessionInit",
        "XrSessionSupportedPermissionDescriptor",
        "XrSpace",
        "XrSystem",
        "XrView",
        "XrViewerPose",
        "XrViewport",
        "XrWebGlLayer",
        "XrWebGlLayerInit",
        "XsltProcessor",
    ]
    .into_iter()
    .collect();
    pub static ref KNOWN_JS_SYS_TYPES: HashSet<&'static str> = [
        "Array",
        "ArrayBuffer",
        "ArrayIter",
        "AsyncIterator",
        "BigInt",
        "BigInt64Array",
        "BigUint64Array",
        "Boolean",
        "DataView",
        "Date",
        "Error",
        "EvalError",
        "Float32Array",
        "Float64Array",
        "Function",
        "Generator",
        "Int8Array",
        "Int16Array",
        "Int32Array",
        "IntoIter",
        "Iter",
        "Iterator",
        "IteratorNext",
        "JsString",
        "Map",
        "Number",
        "Object",
        "Promise",
        "Proxy",
        "RangeError",
        "ReferenceError",
        "RegExp",
        "Set",
        "SharedArrayBuffer",
        "Symbol",
        "SyntaxError",
        "TypeError",
        "Uint8Array",
        "Uint8ClampedArray",
        "Uint16Array",
        "Uint32Array",
        "UriError",
        "WeakMap",
        "WeakSet",
    ]
    .into_iter()
    .collect();
}
