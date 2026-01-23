//! Color generation for categories
//!
//! Generates deterministic colors for each category based on hashing

use super::CategoryInfo;
use std::collections::HashMap;

/// Generate category information with colors
pub fn generate_category_info(
    categories: &HashMap<String, Vec<String>>,
) -> HashMap<String, CategoryInfo> {
    categories
        .iter()
        .map(|(name, constructors)| {
            let colour = category_color(name);
            let info = CategoryInfo {
                name: name.clone(),
                constructors: constructors.clone(),
                colour,
            };
            (name.clone(), info)
        })
        .collect()
}

/// Generate deterministic color for a category
pub fn category_color(category: &str) -> String {
    // Predefined colors for common categories
    match category {
        "Proc" => "208bfe".to_string(), // Blue
        "Name" => "65cda8".to_string(), // Green
        "Elem" => "9966ff".to_string(), // Purple
        _ => {
            // Generate color from hash of category name
            let hash = hash_string(category);
            let hue = hash % 360;
            hsl_to_hex(hue, 70, 60)
        },
    }
}

/// Simple string hash function
fn hash_string(s: &str) -> u32 {
    let mut hash: u32 = 5381;
    for byte in s.bytes() {
        hash = hash.wrapping_mul(33).wrapping_add(byte as u32);
    }
    hash
}

/// Convert HSL to hex color
fn hsl_to_hex(h: u32, s: u32, l: u32) -> String {
    // Simplified HSL to RGB conversion
    let h = h as f64;
    let s = s as f64 / 100.0;
    let l = l as f64 / 100.0;

    let c = (1.0 - (2.0 * l - 1.0).abs()) * s;
    let x = c * (1.0 - ((h / 60.0) % 2.0 - 1.0).abs());
    let m = l - c / 2.0;

    let (r, g, b) = if h < 60.0 {
        (c, x, 0.0)
    } else if h < 120.0 {
        (x, c, 0.0)
    } else if h < 180.0 {
        (0.0, c, x)
    } else if h < 240.0 {
        (0.0, x, c)
    } else if h < 300.0 {
        (x, 0.0, c)
    } else {
        (c, 0.0, x)
    };

    let r = ((r + m) * 255.0) as u8;
    let g = ((g + m) * 255.0) as u8;
    let b = ((b + m) * 255.0) as u8;

    format!("{:02x}{:02x}{:02x}", r, g, b)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_category_colors() {
        assert_eq!(category_color("Proc"), "208bfe");
        assert_eq!(category_color("Name"), "65cda8");

        // Test consistency
        let color1 = category_color("Custom");
        let color2 = category_color("Custom");
        assert_eq!(color1, color2);
    }

    #[test]
    fn test_hex_format() {
        let color = category_color("Test");
        assert_eq!(color.len(), 6);
        assert!(color.chars().all(|c| c.is_ascii_hexdigit()));
    }
}
