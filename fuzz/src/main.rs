fn main() {
    afl::fuzz!(|data: &[u8]| {
        if let Ok(s) = std::str::from_utf8(data) {
            let mut preprocessor = pp_rs::pp::Preprocessor::new(s);
            while let Some(_) = preprocessor.next() {}
        }
    });
}
