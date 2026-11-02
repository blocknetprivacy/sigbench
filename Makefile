.DEFAULT_GOAL := all

OUT     := dist/bench3
LLVM_AR := $$(command -v llvm-ar || echo /opt/homebrew/opt/llvm/bin/llvm-ar)
export RUSTFLAGS := --remap-path-prefix=$(HOME)=/home --remap-path-prefix=$(CURDIR)=/build
export CFLAGS := -ffile-prefix-map=$(CURDIR)=/build
export CXXFLAGS := -ffile-prefix-map=$(CURDIR)=/build

.PHONY: all clean
all:
	@mkdir -p $(OUT)
	cargo build --release -p showcase --target aarch64-apple-darwin
	@cp target/aarch64-apple-darwin/release/showcase $(OUT)/blocknet-bench3-arm64-macos
	AR_x86_64_unknown_linux_gnu=$(LLVM_AR) cargo zigbuild --release -p showcase --target x86_64-unknown-linux-gnu
	@cp target/x86_64-unknown-linux-gnu/release/showcase $(OUT)/blocknet-bench3-amd64-linux
	AR_x86_64_pc_windows_gnu=$(LLVM_AR) cargo zigbuild --release -p showcase --target x86_64-pc-windows-gnu
	@cp target/x86_64-pc-windows-gnu/release/showcase.exe $(OUT)/blocknet-bench3-amd64-windows.exe
	@echo ""
	@echo "3 binaries in $$(pwd)/$(OUT):"
	@ls -1sh $(OUT)

clean:
	cargo clean
	rm -rf $(OUT)
