use crate::surface::ContextTemplate;

const INSERT_PLACEHOLDER: &str = "/* generated theory */";

pub fn lower_context_stub(template: &ContextTemplate) -> String {
    if let Some(offset) = template.insert_offset {
        let mut out = String::new();
        out.push_str(&template.raw[..offset]);
        out.push_str(INSERT_PLACEHOLDER);
        out.push_str(&template.raw[offset + "INSERT_HERE".len()..]);
        out
    } else {
        template.raw.clone()
    }
}
