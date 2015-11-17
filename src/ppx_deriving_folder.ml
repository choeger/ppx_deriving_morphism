(*
 * Copyright (c) 2014, TU Berlin
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *   * Redistributions of source code must retain the above copyright
 *     notice, this list of conditions and the following disclaimer.
 *   * Redistributions in binary form must reproduce the above copyright
 *     notice, this list of conditions and the following disclaimer in the
 *     documentation and/or other materials provided with the distribution.
 *   * Neither the name of the TU Berlin nor the
 *     names of its contributors may be used to endorse or promote products
 *     derived from this software without specific prior written permission.

 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
 * WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL TU Berlin BE LIABLE FOR ANY
 * DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
 * LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
 * ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 *)

(** Generate folder-record(s) for a given type. 

    A fold-function takes the folder (open recursion style), the element being folded, 
    and a value and yields a new value. 
   
    The folder contains fold-functions for each variant of the folded type, e.g.

    type t = Foo of foo | Bar of bar
 
    and foo = { name : string ; wrapped : t }
   
    and bar = Baz | Bax of int

    generates:

    type ('a,'b) fold_fn = ('a t_folder) -> 'b -> 'a -> 'a

    and 'a folder = { on_t : 'a t_folder ; 
                      on_bar : 'a bar_folder 
                    }
    
    and 'a t_folder = { fold_foo : ('a,foo) fold_fn ;
                        fold_bar : ('a,bar) fold_fn }

    and 'a bar_folder = { fold_baz : ('a, unit) fold_fn ;
                          fold_bax : ('a, int) fold_fn }

    let fold_t self = function 
      | Foo foo -> self.t.fold_foo self foo
      | Bar bar -> self.t.fold_bar self bar

    let fold_foo self {name; wrapped} = fold_t self wrapped        

    let fold_bar self = function 
      | Baz -> self.bar.fold_bar ()
      | Bax i -> self.bar.fold_bax i

    let default_t_folder = {
        fold_foo = fold_foo ;
        fold_bar = fold_bar ;
    }

    let default_bar_folder = {
        fold_baz = fold_baz ;
        fold_bax = fold_bax ;
    }
   
    let default_folder = { t = default_t_folder ; bar = default_bar_folder }
*)

open Longident
open Location
open Asttypes
open Parsetree
open Ast_helper
open Ast_convenience
open Ppx_deriving
    
let deriver = "folder"
let raise_errorf = Ppx_deriving.raise_errorf

let tvar x = Typ.var x

let parse_options options =
  options |>
  List.iter (fun (name, expr) ->
      match name with
      | _ -> raise_errorf ~loc:expr.pexp_loc "%s does not support option %s" deriver name)

let attr_fold attrs =
  Ppx_deriving.(attrs |> attr ~deriver "fold" |> Arg.(get_attr ~deriver expr))

let argn =
  Printf.sprintf "arg%d"

let opt_pattn folds =
  List.mapi (fun i e -> match e with Some _ -> pvar (argn i) | None -> Pat.any ()) folds

let pattn typs =
  List.mapi (fun i _ -> pvar (argn i)) typs

let varn typs =
  List.mapi (fun i _ -> evar (argn i)) typs

let pat_tuple = function
  | [] -> Pat.any ()
  | [p] -> p
  | ps -> Pat.tuple ps

let core_type_of_decl ~options ~path type_decl =
  let typ = Ppx_deriving.core_type_of_type_decl type_decl in
  Ppx_deriving.poly_arrow_of_type_decl
    (fun var -> [%type: [%t var] -> [%t var] -> Ppx_deriving_runtime.bool])
    type_decl
    [%type: [%t typ] -> [%t typ] -> Ppx_deriving_runtime.bool]

let sig_of_type ~options ~path type_decl =
  [Sig.value (Val.mk (mknoloc (Ppx_deriving.mangle_type_decl (`Prefix "equal") type_decl))
             (core_type_of_decl ~options ~path type_decl))]

let lift_fold = function
    None -> [%expr fun _ _ x -> x]
  | Some f -> f

let opt_map f x = match x with
    Some y -> Some (f y)
  | None -> None

let rec reduce_fold_seq = function
    [] -> [%expr fun x -> x] (* default serial fold *)
  | (_,None)::es -> reduce_fold_seq es
  | (x,Some f) :: es -> reduce_fold_seq2 [%expr [%e f] [%e x]] es

and reduce_fold_seq2 e = function
    [] -> e
  | (x,Some f) :: es -> reduce_fold_seq2 [%expr (fun f g x -> g (f x)) ([%e e]) ([%e f] [%e x])] es
  | (_, None) :: es -> reduce_fold_seq2 e es

(* generate the fold routine for a given type. 
   Since we might be able to optimize it, in case of unknown types, returns None
   (the identity fold is only used when necessary) *)
let rec expr_of_typ names quoter typ =
  let fold_pass = [%expr fun _ x -> x] in (* 'do nothing' fold-routine *)
  let expr_of_typ : core_type -> expression option = expr_of_typ names quoter in
  match attr_fold typ.ptyp_attributes with
  | Some fn -> Some (Ppx_deriving.quote quoter fn)
  | None ->
    match typ with
    (* Lists can be folded directly *)
    | [%type: [%t? typ] list] ->
      opt_map (fun e -> [%expr List.fold_right [%e e]]) (expr_of_typ typ)
    (* Dito for arrays *)
    | [%type: [%t? typ] array] ->
      opt_map (fun e -> [%expr Array.fold_right [%e e]]) (expr_of_typ typ)
    (* And options *)
    | [%type: [%t? typ] option] ->
      opt_map (fun e -> [%expr fun o x -> match o with None -> x | Some y -> [%e e] y x]) (expr_of_typ typ)
    (* For variables, we expect the corresponding fold function as an argument *)

    (* A tuple, map each element *)
    | { ptyp_desc = Ptyp_tuple typs } ->
      let folds = List.map expr_of_typ typs in
      let pat = pat_tuple (pattn folds) in
      let fold = reduce_fold_seq (List.combine (varn typs) folds) in
      Some [%expr fun [%p pat] -> [%e fold]]

    | { ptyp_desc = Ptyp_var x } ->
      Some (Exp.ident (mknoloc (Lident ("poly_" ^ x))))      
    (* A known constructor (i.e. the name appears in the names arg) *)
    | { ptyp_desc = Ptyp_constr ({ txt = (Lident name) }, args) } when List.mem name names ->
      let fold_fn = Exp.field (evar "self") (mknoloc (Ppx_deriving.mangle_lid (`Prefix "fold") (Lident name))) in

      (* select the approppriate fold_routines for arguments and pass them through *)
      let arg_folds = args |> List.map
                        (fun ct -> match expr_of_typ ct with Some e -> ("", e) | None -> ("", fold_pass))
      in
      if arg_folds = [] then Some [%expr [%e fold_fn] self] else
        Some [%expr [%e Exp.apply fold_fn arg_folds] self]
    | _ -> None
      
type folder = {
  (* all types in the recursive group *)
  names : string list ;

  (* fields *)
  folder_fields : label_declaration list;
  
  (* variant folders *)
  sub_folders : type_declaration list;
  
  (* folder dispatchers *)
  defaults : (Longident.t Location.loc * expression) list ;
}

let rec gather_vars_ct vars = function
  | ({ptyp_desc=Ptyp_var x},_) :: cts -> gather_vars_ct (x::vars) cts
  | _ :: cts -> gather_vars_ct vars cts
  | [] -> vars

and gather_vars vars decl = gather_vars_ct vars decl.ptype_params

let polymorphize arg ct =
  [%type: [%t ct] -> [%t arg] -> [%t arg]]
      
let process_decl quoter fold_arg_t
    {names;sub_folders;defaults;folder_fields}
    ({ ptype_loc = loc } as type_decl) =
  let field_name = Ppx_deriving.mangle_type_decl (`Prefix "fold") type_decl in

  (* create a default implementation (i.e. do nothing but walk the structure) *)
  let on_var = Ppx_deriving.mangle_type_decl (`Prefix "on") type_decl in
  let defaults = match type_decl.ptype_kind with
    | Ptype_variant constrs ->
      (* create a default folder implementation for each variant *)
      let fields =
        constrs |>
        List.map (fun { pcd_name; pcd_args = typs } ->
            let folds = List.map (expr_of_typ names quoter) typs in
            let pat = pat_tuple (opt_pattn folds) in
            let subfield = Ppx_deriving.mangle_lid (`Prefix "fold") (Lident pcd_name.txt) in
            (mknoloc subfield, [%expr fun self [%p pat] -> [%e reduce_fold_seq (List.combine (varn typs) folds)]]))
      in
      (mknoloc (Lident on_var), (Exp.record fields None)) :: defaults
    | _ -> defaults
  in

  let default_var = Ppx_deriving.mangle_type_decl (`Prefix "fold") type_decl in
  let default_fold = match type_decl.ptype_kind with
    |  Ptype_variant constrs ->
      (* create a new dispatcher for a variant type 
         call the appropriate fold-method (see above) 
      *)
      let cases =
        constrs |>
        List.map (fun { pcd_name; pcd_args = typs } ->
            let subfield = Ppx_deriving.mangle_lid (`Prefix "fold") (Lident pcd_name.txt) in
            Exp.case (pconstr pcd_name.txt (pattn typs))
              (Exp.apply 
                     (Exp.field (Exp.field [%expr self] (mknoloc (Lident on_var))) (mknoloc subfield))
                     ["", evar "self"; "", tuple (varn typs)]))
      in      
      [%expr fun self x -> [%e Exp.match_ [%expr x] cases]]                           
    | Ptype_record labels ->
      let folds =
        labels |>
        List.map (fun {pld_name; pld_type} -> 
            evar pld_name.txt, expr_of_typ names quoter pld_type)
      in
      [%expr fun self [%p Pat.record (labels |>
                                      List.map (fun {pld_name} ->
                                          (mknoloc (Lident pld_name.txt)), pvar pld_name.txt)) Closed] -> [%e reduce_fold_seq folds]]
    | Ptype_abstract ->
      begin match type_decl.ptype_manifest with
          Some ct -> begin match expr_of_typ names quoter ct with
              Some f -> [%expr fun self -> [%e f] ]
            | None -> lift_fold None
          end
        | None -> lift_fold None
      end        
    | _ -> lift_fold None
  in
  let defaults = (mknoloc (Lident default_var), (poly_fun_of_type_decl type_decl default_fold))::defaults in

  let params = type_decl.ptype_params |> (List.map (fun (ct,_) -> ct)) in 
  let folded =Typ.constr (mknoloc (Lident type_decl.ptype_name.txt)) params in
  let folder_name = Ppx_deriving.mangle_type_decl (`Suffix "folder") type_decl in
  let (folder_fields, sub_folders) = match type_decl.ptype_kind with
    | Ptype_variant constrs ->
      (* The folder of a variant type is a record with one fold-routine for each variant *)
      let sub_folder_name = Ppx_deriving.mangle_type_decl (`Prefix "on") type_decl in
      let merge_typs = function
          [] -> [%type: ([%t fold_arg_t], unit) fold_routine]
        | [t] -> [%type: ([%t fold_arg_t], [%t t]) fold_routine]
        | ts -> [%type: ([%t fold_arg_t], [%t Typ.tuple ts]) fold_routine]
      in
      (* create the fold_fn signature for the rhs of a constructor *)
      let typs_to_field { pcd_name; pcd_args = typs } =
        Type.field (mknoloc ("fold_" ^ pcd_name.txt)) (merge_typs typs) in
      
      let fields = constrs |> List.map typs_to_field in
      ( (Type.field (mknoloc field_name) [%type: ([%t fold_arg_t], [%t folded]) fold_routine])::
        (Type.field (mknoloc sub_folder_name) (Typ.constr (mknoloc (Lident folder_name)) [fold_arg_t]))::
        folder_fields, 
        (Type.mk
           ~params:[fold_arg_t, Invariant]
           ~kind:(Ptype_record fields) (mknoloc folder_name))::sub_folders )
    | _ ->
      begin 
        (* every other type in the group gets a fold-routine *)
        let vars = gather_vars [] type_decl in
        let routine_t = (poly_arrow_of_type_decl (polymorphize fold_arg_t)
                type_decl [%type: ([%t fold_arg_t], [%t folded]) fold_routine]) in
        ( (Type.field (mknoloc field_name)
             (Typ.poly vars routine_t)
          ) :: folder_fields, sub_folders)
      end

  in {names; sub_folders; defaults; folder_fields}

let folder_to_str fold_arg_t {names; defaults; sub_folders; folder_fields} =
  [
    (Str.type_ (
        Type.mk
          ~params:[fold_arg_t, Invariant]
          ~kind:(Ptype_record folder_fields) (mknoloc "folder") ::
        Type.mk
          ~params:[tvar "a", Invariant; tvar "b", Invariant]
          ~manifest:[%type: 'a folder -> 'b -> 'a -> 'a] (mknoloc "fold_routine") ::
        sub_folders
      )) ;    
    (Str.value Nonrecursive [Vb.mk (pvar "identity_folder") (Exp.record defaults None)]) ;
  ]
  
let str_of_type ~options ~path type_decls =
  parse_options options ;

  let type_vars = List.fold_left gather_vars [] type_decls in    
  let fold_arg_t = tvar (fresh_var type_vars) in
  let quoter = Ppx_deriving.create_quoter () in
  let names = List.map (fun {ptype_name} -> ptype_name.txt) type_decls in
  let folder = (List.fold_left (process_decl quoter fold_arg_t) {names; sub_folders=[]; defaults=[]; folder_fields=[]} type_decls) in
  folder_to_str fold_arg_t folder

let register () =
  Ppx_deriving.(register (create "folder"                              
                            ~type_decl_str: (fun ~options ~path type_decls ->
                                str_of_type ~options ~path type_decls)
                            () ))


let () = register ()
