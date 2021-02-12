fn main() {
    println!("cargo:rerun-if-changed=protos");
    protoc_rust::Codegen::new()
        .customize(protoc_rust::Customize {
            carllerche_bytes_for_bytes: Some(true),
            ..Default::default()
        })
        .out_dir("src/protos")
        .inputs(&["protos/client.proto"])
        .include("protos")
        .run()
        .expect("protoc");
}
