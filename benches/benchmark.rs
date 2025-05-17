use criterion::{criterion_group, criterion_main, Criterion};
use pp_rs::pp::Preprocessor;

pub fn criterion_benchmark(c: &mut Criterion) {
    // Copied from https://github.com/qiutang98/flower/tree/dark/install/shader (MIT License)
    let inputs = std::fs::read_dir("benches/assets")
        .unwrap()
        .map(|d| String::from_utf8(std::fs::read(d.unwrap().path()).unwrap()).unwrap())
        .collect::<Vec<_>>();
    c.bench_function("preprocess", |b| {
        b.iter(|| {
            inputs.iter().for_each(|input| {
                let _ = Preprocessor::new(input).collect::<Vec<_>>();
            })
        })
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
