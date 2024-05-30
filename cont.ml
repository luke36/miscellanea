module Cont = struct
  type ('w, 'a) t = ('a -> 'w) -> 'w
  type ('w, 'a) cont = 'a -> 'w
  type 'a m = {t : 'w. unit -> ('a -> 'w) -> 'w}

  let return x k = k x

  let (>>=) x f k = x (fun y -> f y k)

  let callcc f k = (f k) k

  let throw k x k' = k x

  let run m = m.t () (fun x -> x)
end

(* writing code in the monad is equivalent to the most naieve CPS
   transformation. hopefully the compiler would optimize away most
   of the administrative redexes. *)

(* --> 2 *)
let sb = Cont.(run {t = fun () ->
    callcc (fun k -> callcc (fun k' -> throw k' 1) >>= fun x ->
                     throw k 2 >>= fun y ->
                     return (x + y))
})
