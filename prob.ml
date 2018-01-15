(* Observables are R-valued functions *)
type 'a obs = ('a -> float)

(* By Riesz theorem, probability measures correspond to linear functionals,
   i.e. integrators. *)
type 'a prob = 'a obs -> float

(* A kernel is a function valued in probabilities *)
type ('a, 'b) kernel = 'a -> 'b prob

(* The Dirac kernel (a natural transformation!) *)
let dirac : 'a. 'a -> 'a prob =
  fun x f -> f x

(* Kleisli composition *)
let kleisli : 'a 'b 'c. ('a, 'b) kernel -> ('b, 'c) kernel -> ('a, 'c) kernel =
  fun k1 k2 a f ->
    let prb = k1 a in
    prb (fun b -> 
        let prc = k2 b in
        prc f
      )

(* Pushforward along a kernel *)
let pushforward : 'a 'b. 'a prob -> ('a, 'b) kernel -> 'b prob =
  fun prb k f ->
    prb (fun a -> k a f)

(* Pushforward along a deterministic map*)
let pushforward_det : 'a 'b. 'a prob -> ('a -> 'b) -> 'b prob =
  fun prb k f ->
    prb (fun a -> f (k a))


(* Indicator function of some element *)
let indicator : 'a. 'a -> ('a -> float) =
  fun x y -> 
    if x = y then 1.0 else 0.0

(* Joint probability from a kernel and a measure on the domain *)
let joint : 'a 'b. 'a prob -> ('a, 'b) kernel -> ('a * 'b) prob =
  fun prb k f ->
    prb (fun a -> 
        let ka = k a in
        ka (fun b ->
            f (a, b)
          )
      )

(* Disintegrate a joint probability into a measure and a kernel. Note: conditioning
   on measure 0 sets doesn't work right now. What needs to be done is replacing
   indicator x by a sequence of indicators of a neighbourhood of x that has
   strictly positive mass, inducing a sequence of well-behaved integrals. Of course
   we know that disintegration is not computable, so that cannot be done in
   general (but we can still try, and it would be better).
*)
let disintegrate : 'a 'b. ('a * 'b) prob -> 'a prob * ('a, 'b) kernel =
  fun joint ->
    let d = pushforward_det joint fst in
    let k = fun x ->
      let ix = indicator x in
      let mx = d ix in
      fun f ->
        (joint (fun (x', y) -> (ix x') *. (f y))) /. mx
    in
    (d, k)

let reverse : 'a 'b. ('a * 'b) prob -> ('b * 'a) prob =
  fun joint f ->
    joint (fun (x, y) -> f (y, x))

(* Bayesian inversion *)
let inversion : 
  'a 'b.
  'a prob ->           (* prior *)
  ('a ,'b) kernel ->   (* likelihood *)
  ('b, 'a) kernel =
  fun prb k ->
    let j = joint prb k in
    snd (disintegrate (reverse j))
