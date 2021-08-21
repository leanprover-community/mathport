PKG = Mathport
include $(LEAN4_S1_DIR)/share/lean/lean.mk
all: mathport

MathportEXE=mathport

mathport: $(BIN_OUT)/test
	cp $(BIN_OUT)/test $(MathportEXE)

$(BIN_OUT)/test: $(LIB_OUT)/libMathport.a $(CPP_OBJS) | $(BIN_OUT)
	c++ -rdynamic -o $@ $^ `leanc --print-ldflags`
