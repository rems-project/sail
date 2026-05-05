ifeq ($(OS),Windows_NT)
    LIB_NAME = sail_coverage.lib
else
    LIB_NAME = libsail_coverage.a
endif

$(LIB_NAME): target/release/$(LIB_NAME)
	cp $< $@

target/release/$(LIB_NAME): src/*.rs Cargo.toml Makefile
	cargo build --release

.PHONY: clean

clean:
	rm -f $(LIB_NAME)
	cargo clean
