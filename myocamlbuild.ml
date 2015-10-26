open Ocamlbuild_plugin

let () = dispatch (
  function
  | After_rules ->
    let ppx_loc = (Findlib.query "ppx_deriving").Findlib.location in
    let std_deriver deriver =
       ppx_loc ^ "/" ^ deriver
    in
    flag ["ocaml";"link";"byte";"use_morphism"] &
    A (ppx_loc ^ "/ppx_deriving_runtime.cma") ;

    flag ["ocaml";"link";"native";"use_morphism"] &
    A (ppx_loc ^ "/ppx_deriving_runtime.cmxa") ;
    
    flag ["ocaml"; "compile"; "use_morphism"] &
    S[A"-ppx"; A"ocamlfind ppx_import/ppx_import";
      A"-I"; A ppx_loc ;
      A"-ppx"; A("ocamlfind ppx_deriving/ppx_deriving "^
                 "src/ppx_deriving_folder.cma "^
                 (std_deriver "ppx_deriving_show.cma")) ;
       ]; 
  | _ -> ())
