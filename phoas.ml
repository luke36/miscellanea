module type TERM = sig
  type t

  type term =
    | Var of t
    | App of term * term
    | Abs of (t -> term)
end

module TERMOF(M : sig type t end) : TERM with type t = M.t = struct
  type t = M.t
  type term =
    | Var of t
    | App of term * term
    | Abs of (t -> term)    
end

module type TERM1 =
  functor (T : TERM) -> sig
    val t : T.term
  end

module Loop : TERM1 =
  functor (T : TERM) -> struct
    open T
    let t = App (Abs (fun x -> App (Var x, Var x)),
                 Abs (fun x -> Var x))
  end

module Eval(S : TERM1) = struct
  module U = struct
    type t = term
    and term =
      | Var of t
      | App of term * term
      | Abs of (t -> term)
  end
  module V = S(U)
  open U
  let rec eval t =
    match t with
    | Var x -> x
    | App (t1, t2) -> (
        match eval t1 with
        | Abs f -> eval @@ f (eval t2)
        | _ -> assert false)
    | Abs f -> t
  let r = eval V.t
end

module Print(S : TERM1) = struct
  module U = TERMOF(struct type t = string end)
  module T = S(U)
  open U
  let print t =
    let c = ref 0 in
    let rec pp t =
      match t with
      | Var x -> x
      | App (t1, t2) -> "(" ^ pp t1 ^ " " ^ pp t2 ^ ")"
      | Abs f ->
        let x = "x." ^ string_of_int !c in
        c := !c + 1;
        "(lambda " ^ x ^ " => " ^ pp (f x) ^ ")"
    in
    pp t
  let r = print T.t
end

