build:
	cp pkg/META.in pkg/META
	ocaml pkg/build.ml native=true native-dynlink=true

derive = $(shell ocamlfind query ppx_deriving.show)
dry_run: build
	ocamlfind ppx_tools/rewriter "ocamlfind ppx_deriving/ppx_deriving ${derive}/ppx_deriving_show.cma _build/src/ppx_deriving_folder.cma" src_test/test_ppx_morphism.ml

test: build
	rm -rf _build/src_test/
	ocamlbuild -j 0 -use-ocamlfind -classic-display \
						 src_test/test_ppx_morphism.byte --

clean:
	ocamlbuild -clean

.PHONY: build test doc clean
