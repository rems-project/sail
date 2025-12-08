ifeq ($(OS),Windows_NT)
    LIB_NAME = sail_coverage.lib
else
    LIB_NAME = libsail_coverage.a
endif

target/release/$(LIB_NAME): src/*.rs Cargo.toml Makefile
	cargo build --release
