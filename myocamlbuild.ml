open Ocamlbuild_plugin   

let () = dispatch (
    fun hook ->
      Ocamlbuild_cppo.dispatcher hook ;
      match hook with
      | After_rules ->
        flag ["ocaml"; "compile"; "use_morphism"] &
          Sh(String.chomp (run_and_read
                               "ocamlfind printppx \
                                ppx_deriving ppx_deriving.show \
                                -ppxopt ppx_deriving,src/ppx_deriving_folder.cma \
                                -ppxopt ppx_deriving,src/ppx_deriving_mapper.cma"));
        let add_package tags package =
          flag ("compile" :: "byte" :: tags)
            (Findlib.compile_flags_byte [package]);
          flag ("compile" :: "native" :: tags)
            (Findlib.compile_flags_native [package]);
          flag ("link" :: "byte" :: tags)
            (Findlib.link_flags_byte [package]);
          flag ("link" :: "native" :: tags)
            (Findlib.link_flags_native [package]);
        in
        add_package ["ocaml"; "use_morphism"] (Findlib.query "ppx_deriving.runtime");
      | _ -> ())
