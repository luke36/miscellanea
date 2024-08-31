open Hardcaml
open Hardcaml.Signal

(* putting it together. *)

module I = struct
  type 'a t = { clock : 'a } [@@deriving sexp_of, hardcaml]
end

module O = struct
  type 'a t = { r31_output : 'a [@bits 32] } [@@deriving sexp_of, hardcaml]
end

let create instrs mem_size scope (input : Signal.t I.t) : Signal.t O.t =
  let ( -- ) = Scope.naming scope in
  let clock = input.clock in
  let spec = Reg_spec.create ~clock () in
  let pc' = wire 32 -- "pc'" in
  let pc = reg spec pc' -- "pc" in
  let pc_plus4 = pc +: of_int ~width:32 4 -- "pc+4" in

  let ({ instr } : Signal.t Instr_mem.O.t) =
    Instr_mem.create instrs scope { pc }
  in

  let control =
    Control.create scope { op = instr.:[(31, 26)]; func = instr.:[(5, 0)] }
  in

  let reg_write_data = wire 32 -- "write_data" in
  let reg_addr1 = instr.:[(25, 21)] -- "A1" in
  let reg_addr2 = instr.:[(20, 16)] -- "A2" in
  let ({ read_data1 = reg1; read_data2 = reg2; r31_output }
        : Signal.t Reg_file.O.t) =
    Reg_file.create scope
      {
        clock;
        write_enable = control.reg_write;
        read_addr1 = reg_addr1;
        read_addr2 = reg_addr2;
        write_addr = mux2 control.reg_dst instr.:[(15, 11)] reg_addr2 -- "A3";
        write_data = reg_write_data;
      }
  in

  let imm = sresize instr.:[(15, 0)] 32 -- "imm" in
  let ({ res = alu_res; is_zero } : Signal.t Alu.O.t) =
    Alu.create scope
      {
        src1 = reg1;
        src2 = mux2 control.alu_src imm reg2 -- "src2";
        op = control.alu_control;
      }
  in

  let ({ read_data = mem_read_data } : Signal.t Data_mem.O.t) =
    Data_mem.create mem_size scope
      {
        clock;
        addr = alu_res;
        write_data = reg2;
        write_enable = control.mem_write;
      }
  in

  let pc_branch = pc_plus4 +: sll imm 2 -- "pc_branch" in
  let pc_jump =
    concat_msb [ pc_plus4.:[(31, 28)]; sll (uresize instr.:[(25, 0)] 28) 2 ]
    -- "pc_jump"
  in
  pc'
  <== mux2 control.jump pc_jump
        (mux2 (control.branch &: is_zero) pc_branch pc_plus4);
  reg_write_data <== mux2 control.mem_to_reg mem_read_data alu_res;
  { r31_output }

let hierarchical instrs mem_size (scope : Scope.t) (input : Signal.t I.t) =
  let module H = Hierarchy.In_scope (I) (O) in
  H.hierarchical ~scope ~name:"processor" (create instrs mem_size) input

let create_sim instrs mem_size scope =
  let module Sim = Cyclesim.With_interface (I) (O) in
  Sim.create (create instrs mem_size scope)
