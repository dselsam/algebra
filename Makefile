PKG = Algebra
CPPFLAGS = -O3
include /home/dselsam/omega/lean4/build/current/stage1/share/lean/lean.mk

all: $(BIN_OUT)/test

$(BIN_OUT)/test: $(LIB_OUT)/libAlgebra.a | $(BIN_OUT)
	c++ -rdynamic -o $@ $^ `leanc -print-ldflags`

clear:
	rm -f $(shell find . \( -name "*~" -o -name "*#" \))
