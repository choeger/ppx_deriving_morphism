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

(** Generate mapper-record(s) for a given type. 

    A map-function takes the mapper (open recursion style)
    and a value and yields a new value. 
   
    The mapper contains map-functions for each variant of the folded type, e.g.

    type t = Foo of foo | Bar of bar
 
    and foo = { name : string ; wrapped : t }
   
    and bar = Baz | Bax of int

    generates:

    type ('a,'b) map_fn = t_mapper -> 'a -> 'b

    and mapper = { t : t_mapper ; 
                   bar : bar_mapper;
    }

    and t_mapper = { map_Foo : (foo, t) map_fn ;
                     map_Bar : (bar, t) map_fn }

    and bar_mapper = { map_Baz : (unit, bar) map_fn ;
                       map_Bax : (int, bar) map_fn }

    let map_t self = function 
      | Foo foo -> self.t.map_Foo self foo
      | Bar bar -> self.t.map_Bar self bar

    let map_bar self = function 
      | Baz -> self.bar.map_Bar self ()
      | Bax i -> self.bar.map_Bax self i

    let identity_t_mapper = {
        map_Foo = fun self x -> Foo {x with wrapped = map_t self wrapped}
        map_Bar = fun self x -> Bar (map_bar self x)  
    }

    let identity_bar_mapper = {
        map_Baz = fun self () -> Baz
        map_Bax = fun self x -> Bax x
    }
   
    let identity_mapper = { t = identity_t_mapper ; bar = identity_bar_mapper }
*)

open Longident
open Location
open Asttypes
open Parsetree
open Ast_helper
open Ast_convenience
open Ppx_deriving
    
let deriver = "mapper"
let raise_errorf = Ppx_deriving.raise_errorf

type mapper = {
  (* all types in the recursive group *)
  names : string list ;

  (* fields *)
  mapper_fields : label_declaration list;
  
  (* variant mapper *)
  sub_mappers : type_declaration list;
  
  (* map dispatchers *)
  defaults : (Longident.t Location.loc * expression) list ;
}


let tvar x = Typ.var x

let parse_options options =
  options |>
  List.iter (fun (name, expr) ->
      match name with
      | _ -> raise_errorf ~loc:expr.pexp_loc "%s does not support option %s" deriver name)

let attr_map attrs =
  Ppx_deriving.(attrs |> attr ~deriver "map" |> Arg.(get_attr ~deriver expr))

let argn =
  Printf.sprintf "arg%d"

let opt_pattn maps =
  List.mapi (fun i e -> match e with Some _ -> pvar (argn i) | None -> Pat.any ()) maps

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

let lift_map = function
    None -> [%expr fun _ x -> x]
  | Some f -> f

let opt_map f x = match x with
    Some y -> Some (f y)
  | None -> None

let reduce_map_seq ets =
  (* Reduce a set of mapped arguments by applying all map-routines and create a tuple *)
  let rec reduce_ ds = function
    (* For each argument with a map-routine, apply that routine *)
      [] -> List.rev ds
    | (x,Some f) :: es -> reduce_ ([%expr [%e f] [%e x]]::ds) es
    | (x,None) :: es -> reduce_ (x::ds) es
  in
  
  match reduce_ [] ets with
    [] -> None
  | [e] -> Some e
  | es -> Some (Exp.tuple es)

(* generate the map routine for a given type. 
   In case of unknown types, returns None
*)
let rec expr_of_typ names quoter typ =
  let expr_of_typ : core_type -> expression option = expr_of_typ names quoter in
  let map_pass = [%expr fun x -> x] in
  match attr_map typ.ptyp_attributes with
  | Some fn -> Some (Ppx_deriving.quote quoter fn)
  | None ->
    match typ with
    (* Lists can be mapped directly *)
    | [%type: [%t? typ] list] ->
      opt_map (fun e -> [%expr List.map [%e e]]) (expr_of_typ typ)
    (* Dito for arrays *)
    | [%type: [%t? typ] array] ->
      opt_map (fun e -> [%expr Array.map [%e e]]) (expr_of_typ typ)
    (* And options *)
    | [%type: [%t? typ] option] ->
      opt_map (fun e -> [%expr fun o -> match o with None -> None | Some y -> Some ([%e e] y)]) (expr_of_typ typ)
    (* For variables, we expect the corresponding map function as an argument *)
    | { ptyp_desc = Ptyp_var x } ->
      Some (Exp.ident (mknoloc (Lident ("poly_" ^ x))))

    (* A tuple, map each element *)
    | { ptyp_desc = Ptyp_tuple typs } ->
      let maps = List.map expr_of_typ typs in
      let pat = pat_tuple (pattn maps) in
      let map = match reduce_map_seq (List.combine (varn typs) maps) with
          Some e -> e
        | None -> raise (Failure "Tuple invariant broken")
      in
      Some [%expr fun [%p pat] -> [%e map]]
      
    (* A known constructor (i.e. the name appears in the names arg) 
       We expect a map_<t> function to exist 
    *)
    | { ptyp_desc = Ptyp_constr ({ txt = (Lident name) }, args) } when List.mem name names ->
      let map_fn = Exp.field (evar "self") (mknoloc (Ppx_deriving.mangle_lid (`Prefix "map") (Lident name))) in

      (* select the approppriate map_routines for arguments and pass them through *)
      let arg_maps = args |> List.map
                       (fun ct -> match expr_of_typ ct with Some e -> ("", e) | None -> ("", map_pass))
      in
      if arg_maps = [] then Some [%expr [%e map_fn] self] else
        Some [%expr [%e Exp.apply map_fn arg_maps] self]
    | _ -> None
      
let rec gather_vars_ct vars = function
  | ({ptyp_desc=Ptyp_var x},_) :: cts -> gather_vars_ct (x::vars) cts
  | _ :: cts -> gather_vars_ct vars cts
  | [] -> vars

and gather_vars vars decl = gather_vars_ct vars decl.ptype_params

let polymorphize ct =
  [%type: [%t ct] -> [%t ct]]
                       
let process_decl quoter
    {names;sub_mappers;defaults;mapper_fields}
    ({ ptype_loc = loc } as type_decl) =
  let field_name = Ppx_deriving.mangle_type_decl (`Prefix "map") type_decl in

  (* create a default implementation (i.e. do nothing but walk the structure) *)
  let on_var = Ppx_deriving.mangle_type_decl (`Prefix "on") type_decl in
  let defaults = match type_decl.ptype_kind with
    | Ptype_variant constrs ->
      (* create a default mapper implementation for each variant *)
      let fields =
        constrs |>
        List.map (fun { pcd_name; pcd_args = typs } ->
            let maps = List.map (expr_of_typ names quoter) typs in
            let pat = pat_tuple (pattn maps) in
            let subfield = Ppx_deriving.mangle_lid (`Prefix "map") (Lident pcd_name.txt) in
            (mknoloc subfield, [%expr fun self [%p pat] ->
                     [%e
                       (Exp.construct
                          {pcd_name with txt=Lident pcd_name.txt}
                          (reduce_map_seq (List.combine (varn typs) maps)))]
              ]))
      in
      (mknoloc (Lident on_var), (Exp.record fields None)) :: defaults
    | _ -> defaults
  in

  let default_var = Ppx_deriving.mangle_type_decl (`Prefix "map") type_decl in
  let default_map = match type_decl.ptype_kind with
    |  Ptype_variant constrs ->
      (* create a new dispatcher for a variant type 
         call the appropriate map-method (see above) 
      *)
      let cases =
        constrs |>
        List.map (fun { pcd_name; pcd_args = typs } ->
            let subfield = Ppx_deriving.mangle_lid (`Prefix "map") (Lident pcd_name.txt) in
            Exp.case (pconstr pcd_name.txt (pattn typs))
              (Exp.apply 
                 (Exp.field
                    (Exp.field [%expr self] (mknoloc (Lident on_var)))
                    (mknoloc subfield))
                 ["", evar "self"; "", tuple (varn typs)]))
      in      
      [%expr fun self x -> [%e Exp.match_ [%expr x] cases]]                           
    | Ptype_record labels ->
      (* map all fields of a record *)
      let maps =
        labels |>
        List.map begin
          fun {pld_name; pld_type} ->
            ({pld_name with txt = Lident pld_name.txt}, 
             match expr_of_typ names quoter pld_type with
               None -> evar pld_name.txt
             | Some map -> Exp.apply map ["", evar pld_name.txt]
            )
        end                  
      in
      let pattern = Pat.record
          (labels |>
           List.map (fun {pld_name} ->
               (mknoloc (Lident pld_name.txt)), pvar pld_name.txt)) Closed
      in
      [%expr fun self [%p pattern]  -> [%e Exp.record maps None] ]

    | Ptype_abstract ->
      begin match type_decl.ptype_manifest with
          Some ct -> begin match expr_of_typ names quoter ct with
              Some f -> [%expr fun self -> [%e f]]
            | None -> lift_map None
          end
        | None -> lift_map None
      end
    | _ -> lift_map None
  in
  let defaults = (mknoloc (Lident default_var), (poly_fun_of_type_decl type_decl default_map))::defaults in

  let params = type_decl.ptype_params |> (List.map (fun (ct,_) -> ct)) in 
  let mapped = Typ.constr
      {type_decl.ptype_name with txt = Lident type_decl.ptype_name.txt}
      params in
  let mapper_name = Ppx_deriving.mangle_type_decl (`Suffix "mapper") type_decl in
  let (mapper_fields, sub_mappers) = match type_decl.ptype_kind with
    | Ptype_variant constrs ->
      (* The mapper of a variant type is a record with one map-routine for each variant *)
      let sub_mapper_name = Ppx_deriving.mangle_type_decl (`Prefix "on") type_decl in
      
      let merge_typs = function
          [] -> [%type: (unit, [%t mapped]) map_routine]
        | [t] -> [%type: ([%t t], [%t  mapped]) map_routine]
        | ts -> [%type: ([%t Typ.tuple ts], [%t mapped]) map_routine]
      in
      
      (* create the map_fn signature for the rhs of a constructor *)
      let typs_to_field { pcd_name; pcd_args = typs } =
        Type.field (mknoloc ("map_" ^ pcd_name.txt)) (merge_typs typs) in
      
      let fields = constrs |> List.map typs_to_field in
      ( (Type.field (mknoloc field_name) [%type: ([%t mapped], [%t mapped]) map_routine])::
        (Type.field (mknoloc sub_mapper_name) (Typ.constr (mknoloc (Lident mapper_name)) []))::
        mapper_fields, 
        (Type.mk
           ~kind:(Ptype_record fields) (mknoloc mapper_name))::sub_mappers )
    | _ ->
      begin 
        (* every other type in the group gets a map-routine *)
        let vars = gather_vars [] type_decl in
        let routine_t = (poly_arrow_of_type_decl polymorphize
                type_decl [%type: ([%t mapped], [%t mapped]) map_routine]) in
        ( (Type.field (mknoloc field_name)
             (Typ.poly vars routine_t)
          ) :: mapper_fields, sub_mappers)
      end

  in {names; sub_mappers; defaults; mapper_fields}

let mapper_to_str {names; defaults; sub_mappers; mapper_fields} =
  [
    (Str.type_ (
        Type.mk
          ~kind:(Ptype_record mapper_fields) (mknoloc "mapper") ::
        Type.mk
          ~params:[tvar "a", Invariant; tvar "b", Invariant]
          ~manifest:[%type: mapper -> 'a -> 'b] (mknoloc "map_routine") ::

        sub_mappers
      )) ;    
    (Str.value Nonrecursive [Vb.mk (pvar "identity_mapper") (Exp.record defaults None)]) ;
  ]
  
let str_of_type ~options ~path type_decls =
  parse_options options ;

  let quoter = Ppx_deriving.create_quoter () in
  let names = List.map (fun {ptype_name} -> ptype_name.txt) type_decls in
  let mapper = (List.fold_left (process_decl quoter) {names; sub_mappers=[]; defaults=[]; mapper_fields=[]} type_decls) in
  mapper_to_str mapper

let register () =
  Ppx_deriving.(register (create "mapper"                              
                            ~type_decl_str: (fun ~options ~path type_decls ->
                                str_of_type ~options ~path type_decls)
                            () ))


let () = register ()
