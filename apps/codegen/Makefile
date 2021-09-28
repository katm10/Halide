include ../support/Makefile.inc

OBJECTS = $(BIN)/Printer.o $(BIN)/Language.o

all: $(BIN)/MergeTool

CXXFLAGS += -O3 -g

LDFLAGS += -L ../../distrib/bin -L ../../distrib/lib -Wl,-rpath ../../distrib/lib

STATIC_LDFLAGS = $(filter-out -lpthread,$(LDFLAGS)) -pthread -Wl,--whole-archive -lpthread -Wl,--no-whole-archive

$(BIN)/%.o: %.cpp %.h
	@mkdir -p $(@D)
	$(CXX) $(CXXFLAGS) -c $< -o $@

$(BIN)/MergeTool: MergeTool.cpp $(OBJECTS) $(LIB_HALIDE)
	@mkdir -p $(@D)
	$(CXX) $(CXXFLAGS) $< $(OBJECTS) -o $@ $(LDFLAGS) -lHalide

clean:
	rm -rf $(BIN)