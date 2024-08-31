open Hardcaml
open Hardcaml.Signal

module I = struct
  type 'a t = { op : 'a; [@bits 6] func : 'a [@bits 6] }
  [@@deriving sexp_of, hardcaml]
end

module O = struct
  type 'a t = {
    mem_to_reg : 'a;
    mem_write : 'a;
    branch : 'a;
    alu_control : 'a; [@bits 3]
    alu_src : 'a;
    reg_dst : 'a;
    reg_write : 'a;
    jump : 'a;
  }
  [@@deriving sexp_of, hardcaml]
end

let create scope (input : Signal.t I.t) : Signal.t O.t =
  let ( -- ) = Scope.naming scope in
  let op0 = input.op.:[(0, 0)] in
  let op1 = input.op.:[(1, 1)] in
  let op2 = input.op.:[(2, 2)] in
  let op3 = input.op.:[(3, 3)] in

  let jump = (op0 ^: op1) -- "jump" in
  let mem_to_reg = op0 -- "mem_to_reg" in
  let mem_write = (op1 &: op3) -- "mem_write" in
  let branch = op2 -- "branch" in
  let alu_src = (op0 |: op3) -- "alu_src" in
  let reg_dst = ~:(op1 |: op2 |: op3) -- "reg_dst" in
  let reg_write = (~:op2 &: (~:op1 |: op0 ^: op3)) -- "reg_write" in

  let c_add = of_string "010" in
  let c_sub = of_string "110" in
  let c_and = of_string "000" in
  let c_or = of_string "001" in
  let c_slt = of_string "111" in

  let f0 = input.func.:[(0, 0)] in
  let f1 = input.func.:[(1, 1)] in
  let f2 = input.func.:[(2, 2)] in
  let f3 = input.func.:[(3, 3)] in
  let alu_control =
    mux2 (op0 |: op3) c_add
      (mux2 op2 c_sub
         (mux2 f1 (mux2 f3 c_slt c_sub) (mux2 f2 (mux2 f0 c_or c_and) c_add)))
    -- "alu_control"
  in
  (* there should be some much cleaner way ... *)
  {
    mem_to_reg;
    mem_write;
    branch;
    alu_control;
    alu_src;
    reg_dst;
    reg_write;
    jump;
  }

let hierarchical (scope : Scope.t) (input : Signal.t I.t) =
  let module H = Hierarchy.In_scope (I) (O) in
  H.hierarchical ~scope ~name:"control_unit" create input

let create_sim scope =
  let module Sim = Cyclesim.With_interface (I) (O) in
  Sim.create (create scope)
