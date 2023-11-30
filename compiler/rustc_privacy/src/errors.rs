use rustc_errors::DiagnosticArgFromDisplay;
use rustc_macros::{Diagnostic, LintDiagnostic, Subdiagnostic};
use rustc_span::{Span, Symbol};

#[derive(Diagnostic)]
#[diag(privacy_field_is_private, code = "E0451")]
pub struct FieldIsPrivate {
    #[primary_span]
    pub span: Span,
    pub field_name: Symbol,
    pub variant_descr: &'static str,
    pub def_path_str: String,
    #[subdiagnostic]
    pub label: FieldIsPrivateLabel,
}

#[derive(Subdiagnostic)]
pub enum FieldIsPrivateLabel {
    #[label(privacy_field_is_private_is_update_syntax_label)]
    IsUpdateSyntax {
        #[primary_span]
        span: Span,
        field_name: Symbol,
    },
    #[label(privacy_field_is_private_label)]
    Other {
        #[primary_span]
        span: Span,
    },
}

#[derive(Diagnostic)]
#[diag(privacy_item_is_private)]
pub struct ItemIsPrivate<'a> {
    #[primary_span]
    #[label]
    pub span: Span,
    pub kind: &'a str,
    pub descr: DiagnosticArgFromDisplay<'a>,
}

#[derive(Diagnostic)]
#[diag(privacy_unnamed_item_is_private)]
pub struct UnnamedItemIsPrivate {
    #[primary_span]
    pub span: Span,
    pub kind: &'static str,
}

#[derive(Diagnostic)]
#[diag(privacy_in_public_interface, code = "E0446")]
pub struct InPublicInterface<'a> {
    #[primary_span]
    #[label]
    pub span: Span,
    pub vis_descr: &'static str,
    pub kind: &'a str,
    pub descr: DiagnosticArgFromDisplay<'a>,
    #[label(privacy_visibility_label)]
    pub vis_span: Span,
}

#[derive(Diagnostic)]
#[diag(privacy_report_effective_visibility)]
pub struct ReportEffectiveVisibility {
    #[primary_span]
    pub span: Span,
    pub descr: String,
}

#[derive(LintDiagnostic)]
#[diag(privacy_from_private_dep_in_public_interface)]
pub struct FromPrivateDependencyInPublicInterface<'a> {
    pub kind: &'a str,
    pub descr: DiagnosticArgFromDisplay<'a>,
    pub krate: Symbol,
}

#[derive(LintDiagnostic)]
#[diag(privacy_unnameable_types_lint)]
pub struct UnnameableTypesLint<'a> {
    #[label]
    pub span: Span,
    pub kind: &'a str,
    pub descr: DiagnosticArgFromDisplay<'a>,
    pub reachable_vis: &'a str,
    pub reexported_vis: &'a str,
}

// Used for `private_interfaces` and `private_bounds` lints.
// They will replace private-in-public errors and compatibility lints in future.
// See https://rust-lang.github.io/rfcs/2145-type-privacy.html for more details.
#[derive(LintDiagnostic)]
#[diag(privacy_private_interface_or_bounds_lint)]
pub struct PrivateInterfacesOrBoundsLint<'a> {
    #[label(privacy_item_label)]
    pub item_span: Span,
    pub item_kind: &'a str,
    pub item_descr: DiagnosticArgFromDisplay<'a>,
    pub item_vis_descr: &'a str,
    #[note(privacy_ty_note)]
    pub ty_span: Span,
    pub ty_kind: &'a str,
    pub ty_descr: DiagnosticArgFromDisplay<'a>,
    pub ty_vis_descr: &'a str,
}
