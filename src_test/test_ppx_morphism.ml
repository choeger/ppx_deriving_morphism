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

open OUnit2
    
let fold_int _ x sum = x + sum

module Test1 = struct
  (** Just run over some basic foo-structures *)
  type foo = {x : int; y : int} 

  and bar = { lhs : baz; rhs : foo}
            
  and baz = Foo of foo | Bar of bar [@@deriving folder,mapper]

  let sum = { identity_folder with fold_foo = (fun self {x;y} z -> x + y + z) } 

  let test_int_record ctxt =
    assert_equal ~printer:string_of_int 3 (sum.fold_foo sum {x=2;y=1} 0) ;
    assert_equal ~printer:string_of_int 42 (sum.fold_baz sum (Bar {lhs=Foo{x=1;y=1}; rhs={x=0;y=40}}) 0)
      
  let float_sum = { identity_folder with fold_foo = (fun self {x;y} z -> (float_of_int x) +. (float_of_int y) +. z) }

  let test_float_record ctxt =
    assert_equal ~printer:string_of_float 3. (float_sum.fold_foo float_sum {x=2;y=1} 0.0) ;
    assert_equal ~printer:string_of_float 42. (float_sum.fold_baz float_sum (Bar {lhs=Foo{x=1;y=1}; rhs={x=0;y=40}}) 0.)

  let zero = { identity_mapper with map_foo = (fun self _ -> {x=0;y=0}) }

  let test_zero ctxt =
    assert_equal {x=0;y=0} (zero.map_foo zero {x=42;y=23}) 

end 

type fvs = string list [@@deriving show]
let filter x fvs = List.filter (fun y -> not (y = x)) fvs
let cons x xs = x::xs

module Test2 = struct
  (** Basic use case: free variables of a simple lambda calculus *)
  
  type expr = Abs of abs
            | App of app
            | Let of let_
            | Int of int
            | Sel of expr * string
            | Var of string

  and abs = { abs_var : string; abs_rhs : expr }

  and app = { lhs : expr; rhs : expr }

  and let_ = {let_var : string; let_bdy : expr ; let_rhs : expr}
    [@@deriving folder, mapper]  

  let (%>) f g x = g (f x)
  let fv_folder = { identity_folder with fold_abs = (fun self {abs_var; abs_rhs} -> self.fold_expr self abs_rhs %> (filter abs_var)) ;
                                         fold_let_ = (fun self {let_var; let_bdy; let_rhs} ->
                                             self.fold_expr self let_bdy %>
                                             filter let_var %>
                                             self.fold_expr self let_rhs ) ;
                                         on_expr = { identity_folder.on_expr with fold_Var = (fun self -> cons) }
                  }

  let fv e = fv_folder.fold_expr fv_folder e []

  let upper_case_mapper = { identity_mapper with on_expr = { identity_mapper.on_expr with map_Var = fun _ x -> Var (String.uppercase x) ;} ;
                                                 map_abs = ( fun self {abs_var; abs_rhs} -> {abs_rhs = self.map_expr self abs_rhs ;
                                                                                             abs_var = String.uppercase abs_var } ) ;
                                                 map_let_= ( fun self {let_var; let_bdy; let_rhs} ->
                                                     { let_var = String.uppercase let_var ;
                                                       let_bdy = self.map_expr self let_bdy ;
                                                       let_rhs = self.map_expr self let_rhs } ) ;
                          }

  let upper_case = upper_case_mapper.map_expr upper_case_mapper 
  
  let test ctxt = 
    assert_equal ~printer:show_fvs ["x"] (fv (Var "x")) ;
    assert_equal ~printer:show_fvs ["x"] (fv (Sel (Var "x", "foo"))) ;
    assert_equal ~printer:show_fvs ["x"] (fv (Abs {abs_var="y"; abs_rhs = App {lhs = Var "x"; rhs = Var "y"}})) ;
    assert_equal ~printer:show_fvs [] (fv (Let {let_var="x"; let_rhs=Int 0; let_bdy=Abs {abs_var="y"; abs_rhs = App {lhs = Var "x"; rhs = Var "y"}}})) 

  let test_mapper ctxt =
    assert_equal ~printer:show_fvs ["X"] (fv (upper_case (Var "x"))) ;    
    assert_equal ~printer:show_fvs ["X"] (fv (upper_case (Sel (Var "x", "foo")))) ;
    assert_equal ~printer:show_fvs ["X"] (fv (upper_case (Abs {abs_var="y"; abs_rhs = App {lhs = Var "x"; rhs = Var "y"}}))) ;
    assert_equal ~printer:show_fvs [] (fv (upper_case (Let {let_var="x"; let_rhs=Int 0; let_bdy=Abs {abs_var="y"; abs_rhs = App {lhs = Var "x"; rhs = Var "y"}}}))) 
    
end

module PolyTest = struct
  (** Somewhat more complicated: reuse binding structure *)
  
  type expr = Abs of unit binding
            | App of app
            | Let of expr binding
            | Var of string
            | Int of int
  
  and app = { lhs : expr; arg : expr }

  and 'a binding = { var : string ; rhs : 'a; bdy : expr }
                   [@@deriving folder,mapper]

  let filter x fvs = List.filter (fun y -> not (y = x)) fvs
  let cons x xs = x::xs

  let (%>) f g x = g (f x)
  let fv_folder = { identity_folder with
                    fold_binding =
                      (fun f self {var;rhs;bdy} ->
                         self.fold_expr self bdy %>
                         filter var %>
                         f rhs ) ;
                    on_expr = { identity_folder.on_expr with fold_Var = (fun self -> cons) }
                  }

  let upper_case_mapper = { identity_mapper with
                            map_binding = (fun f self {var;rhs;bdy} -> {var=String.uppercase var; rhs=f rhs; bdy=self.map_expr self bdy}) ;
                            on_expr = { identity_mapper.on_expr with map_Var = fun _ x -> Var (String.uppercase x) ; } ;
                          }

  let upper_case = upper_case_mapper.map_expr upper_case_mapper 
    
  let fv e = fv_folder.fold_expr fv_folder e []

  let test ctxt = 
    assert_equal ~printer:show_fvs ["z"] (fv (Var "z")) ;
    assert_equal ~printer:show_fvs ["t"]
      (fv (Let {var="s"; rhs=Int 0; bdy = App {lhs = Var "t"; arg = Var "s"}})) ;
    assert_equal ~printer:show_fvs ["x"]
      (fv (Abs {var="y"; rhs=(); bdy = App {lhs = Var "x"; arg = Var "y"}})) ;
    assert_equal ~printer:show_fvs []
      (fv (Let{var="a"; rhs=Int 0;
               bdy=Abs {var="b"; rhs = ();
                        bdy= App {lhs = Var "a"; arg = Var "b"}}})) 

  let test_mapper ctxt = 
    assert_equal ~printer:show_fvs ["Z"] (fv (upper_case (Var "z"))) ;
    assert_equal ~printer:show_fvs ["T"]
      (fv (upper_case (Let {var="s"; rhs=Int 0; bdy = App {lhs = Var "t"; arg = Var "s"}}))) ;
    assert_equal ~printer:show_fvs ["X"]
      (fv (upper_case (Abs {var="y"; rhs=(); bdy = App {lhs = Var "x"; arg = Var "y"}}))) ;
    assert_equal ~printer:show_fvs []
      (fv (upper_case(Let{var="a"; rhs=Int 0;
                          bdy=Abs {var="b"; rhs = ();
                                   bdy= App {lhs = Var "a"; arg = Var "b"}}}))) 

end

module PolyRecTest = struct
  (** Even more complicated, reuse pairing structure *)
  
  type expr = Abs of abs_binding
            | App of (expr,expr) pair
            | Let of expr binding
            | Var of string
            | Int of my_int

  and my_int = int
  
  and ('a,'b) pair = { lhs : 'a ; rhs : 'b }

  and abs_binding = unit binding
  
  and 'a binding = { var : string ; terms : (expr, 'a) pair }
    [@@deriving folder,mapper]

  let (%>) f g x = g (f x)
  let fv_folder = { identity_folder with
                  fold_binding =
                    (fun f self {var;terms={rhs;lhs}} ->
                      self.fold_expr self lhs %>
                      filter var %>
                      f rhs ) ;
                  on_expr = { identity_folder.on_expr with fold_Var = (fun self -> cons) }
                }
  
  let fv e = fv_folder.fold_expr fv_folder e []

  let upper_case_mapper = { identity_mapper with
                            map_binding = (fun f self {var;terms={rhs;lhs}} -> {var=String.uppercase var; terms={rhs=f rhs; lhs=self.map_expr self lhs}}) ;
                            on_expr = { identity_mapper.on_expr with map_Var = fun _ x -> Var (String.uppercase x) ; } ;
                          }

  let upper_case = upper_case_mapper.map_expr upper_case_mapper 
  
  let test ctxt = 
    assert_equal ~printer:show_fvs ["z"] (fv (Var "z")) ;
    assert_equal ~printer:show_fvs ["t"]
      (fv (Let {var="s"; terms={rhs = Int 0;
                                lhs = App {lhs = Var "t"; rhs = Var "s"}}})) ;
    assert_equal ~printer:show_fvs ["x"]
      (fv (Abs {var="y"; terms = { rhs=();
                                   lhs = App {lhs = Var "x"; rhs = Var "y" }}})) ;
    assert_equal ~printer:show_fvs []
      (fv (Let{var="a";
               terms= { rhs=Int 0;
                        lhs=Abs {var="b";
                                 terms={
                                   rhs = ();
                                   lhs = App {lhs = Var "a"; rhs = Var "b"}}}}})) 

  let test_mapper ctxt = 
    assert_equal ~printer:show_fvs ["Z"] (fv (upper_case (Var "z"))) ;
    assert_equal ~printer:show_fvs ["T"]
      (fv (upper_case (Let {var="s"; terms={rhs = Int 0;
                                            lhs = App {lhs = Var "t"; rhs = Var "s"}}}))) ;
    assert_equal ~printer:show_fvs ["X"]
      (fv (upper_case (Abs {var="y"; terms = { rhs=();
                                               lhs = App {lhs = Var "x"; rhs = Var "y" }}}))) ;
    assert_equal ~printer:show_fvs []
      (fv (upper_case (Let{var="a";
                           terms= { rhs=Int 0;
                                    lhs=Abs {var="b";
                                             terms={
                                               rhs = ();
                                               lhs = App {lhs = Var "a"; rhs = Var "b"}}}}}))) 

end

module TupleTest = struct
  (** A simple binary tree *)

  type node = Node of int * children
  and children = tree * tree
  and foo = children * tree option
  and tree = node option
    [@@deriving folder,mapper,show]
    
  let insertion_mapper n = {identity_mapper with
                            map_node =
                              (fun self (Node (m,(left,right))) ->
                                 if n = m then Node (m,(left,right)) else
                                 if n < m then Node (m, ((self.map_tree self left), right))
                                 else Node (m, (left, self.map_tree self right))
                              ) ;
                            map_tree = (fun self -> function None -> Some (Node (n, (None, None)))
                                                           | Some node -> Some (self.map_node self node)
                              );
                           }

  let insert i t = let m = insertion_mapper i in m.map_tree m t

  let incr_mapper = {identity_mapper with
                     (* Node vs. node test *)
                     on_node = {
                       map_Node = (fun self (n,children) -> Node (n + 1, self.map_children self children))
                     };
                    }

  let inc = incr_mapper.map_tree incr_mapper

  let sum_folder = {identity_folder with
                    on_node = {
                      fold_Node = (fun self (n,children) sum -> self.fold_children self children (n + sum)) ;
                    }
                   }

  let sum t = sum_folder.fold_tree sum_folder t 0
  
  let test_mapper ctxt =
    assert_equal ~printer:show_tree (Some (Node (2, (Some (Node (1, (None, None))), None)))) (insert 1 (insert 2 None)) ;
    assert_equal ~printer:show_tree (Some (Node (3, (Some (Node (2, (None, None))), None)))) (inc (insert 1 (insert 2 None))) 

  let test_folder ctxt =
    assert_equal ~printer:string_of_int 5 (sum (inc (insert 1 (insert 2 None))))
                                   
end

let suite = "Test ppx_morphism" >::: [
    "test_int_record" >:: Test1.test_int_record ;
    "test_float_record" >:: Test1.test_float_record ;
    "test zero mapper" >:: Test1.test_zero ;
    "test fv" >:: Test2.test ;
    "test uppercase mapper" >:: Test2.test_mapper ;
    "test poly fv" >:: PolyTest.test ;
    "test poly mapper" >:: PolyTest.test_mapper ;
    "test poly recursive fv" >:: PolyRecTest.test ;    
    "test poly recursive mapper" >:: PolyRecTest.test_mapper ;
    "Tuple and option mapper" >:: TupleTest.test_mapper ;
    "Tuple and option folder" >:: TupleTest.test_folder ;    
  ]

let _ =
  run_test_tt_main suite

