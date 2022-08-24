use builtin_macros::*;
use builtin::*;
mod pervasive;
use pervasive::string::*;

verus! {
    fn test_get_unicode_non_ascii_passes() {
        let emoji_with_str = new_strlit("💩");
        proof {
            reveal_strlit("💩");
        }
        let emoji = emoji_with_str.get_char(0);
        assert(emoji == '💩');
    }
}
fn main() {}

