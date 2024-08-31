open Base
open Hardcaml

let sum =
  List.map ~f:Signal.of_string
    [
      (* r1 = r2 = r3 = out = 0 *)
      "00100000010000100111111111111111" (* r2 <- ... *);
      "00100000001000010000000000000001" (* r1 <- r1 + 1 *);
      "00000000001000110001100000100000" (* r3 <- r3 + r1 *);
      "00010000001000100000000000000001" (* if r1=r2 -> 12+4+4 *);
      "00001000000000000000000000000001" (* j 4 *);
      "00000000011111111111100000100000" (* out <- r3 *);
      "00001000000000000000000000000110" (* j 24 *);
    ]

let () =
  let mem_size = 512 in
  let scope = Scope.create ~flatten_design:true () in
  let sim = Processor.create_sim sum mem_size scope in
  let output = (Cyclesim.outputs sim).r31_output in
  let rec step acc =
    (*    ignore @@ Stdlib.read_line ();*)
    Cyclesim.cycle sim;
    if Bits.to_int !output = 0 then step (acc + 1)
    else (
      Stdio.printf "%s\n" @@ Bits.to_string !output;
      acc)
  in

  let scope' = Scope.create () in
  let proc =
    Processor.hierarchical sum mem_size scope'
      { clock = Signal.input "clock" 1 }
  in
  let circuit =
    Circuit.create_exn ~name:"mips"
      [ Signal.output "r31_output" proc.r31_output ]
  in
  Stdio.printf "\n";
  Rtl.print ~database:(Scope.circuit_database scope') Verilog circuit;
  Stdio.printf "\n";
  Stdio.printf "%d\n" @@ step 0
