(* Bayesian inference over finite spaces *)

(* We model finite sets by lists. Really, ['a set] is the type of finite subsets of other types.
 * If we were doing this in Coq we could just use finite sets. *)
type 'a set = 'a list

(* A probability over a finite set is given by its support and by a function
 * assigning a real value to each atom. Here, several invariants are not enforced:
 * positivity and normalisation. The type system isn't rich enough. *)
type 'a prob =
  {
    support : 'a set;
    prb     : 'a -> float
  }

(* A kernel a finite subset (its domain) to a finite subset (its codomain) is a map from 
 * the elements of its domain to probabilities over its codomain.
 * Here, an invariant is not expressed in the type: for all $x \in dom$, $kern(x)$ should
 * be a probability with $support$ equal to $cod$. *)
type ('a, 'b) kernel =
  {
    dom  : 'a set;
    cod  : 'b set;
    kern : 'a -> 'b prob
  }

(* printers *)
let print_prob : 'a. ('a -> string) -> 'a prob -> string =
  fun tostr prob ->
  List.fold_left (fun acc x ->
      let p = prob.prb x in
      Printf.sprintf "%s = %f;%s" (tostr x) p acc
    ) "" prob.support
    
(* The dirac natural transformation *)    
let dirac : 'a. 'a -> 'a prob =
  fun x ->
  { support = [x];
    prb     = fun y ->
              if x = y then 1.0
              else 0.0
  }

(* Uniform probability on a finite space. *)    
let uniform : 'a. 'a set -> 'a prob =
  fun l ->
  match l with
  | [] -> failwith "empty list"
  | hd :: tl ->
     let ilen = 1.0 /. float (List.length l) in
     { support = l;
       prb     = fun y -> ilen }

(* Sample from a probability. Intuitively, we look at the cumulative distrbution
 * function of a probability, make a pie out of it with one slice per atom and where the slices
 * are proportional to the area, and draw uniformly at random on the pie (here the pie is the [0,1] interval). 
 *)
let sample : 'a. 'a prob -> 'a =
  fun prob ->
  let r = Random.float 1.0 in
  let _, res =
    List.fold_left (fun ((cumu, opt) as acc) elt ->
                    let cumu = cumu +. (prob.prb elt) in
                    match opt with
                    | None ->
                       if r <= cumu then
                         (cumu, Some elt)
                       else
                         (cumu, None)
                    | Some _ ->
                       acc
                   ) (0.0, None) prob.support
  in match res with
     | Some res -> res
     | None -> failwith "sample failed"

(* [iid prob n] gives a random vector of size n, iid dstributed according to prob *)                        
let rec iid : 'a. 'a prob -> int -> 'a list =
  fun prob n ->
  if n = 0 then
    []
  else
    (sample prob) :: (iid prob (n - 1))

(* Gets a sequence (a multiset really) of data and computes the empirical distribution *)                       
let empirical : 'a. 'a list -> 'a prob =
  function
  | [] ->
     failwith "empirical: probability with empty support"
  | list ->
     let ilen = 1.0 /. float (List.length list) in
     {
       support = list;
       prb     = fun x ->
                 let c = List.length (List.filter (fun y -> y = x) list) in
                 (float c) *. ilen
     }

(* Family of identity kernels parameterised by underlying set. *)
let identity : 'a. 'a set -> ('a, 'a) kernel =
  fun set ->
  { dom = set;
    cod = set;
    kern = fun x -> dirac x
  }

(* The kleisli composition, i.e the composition of kernels. *)    
let kleisli : 'a 'b 'c. ('a, 'b) kernel -> ('b, 'c) kernel -> ('a, 'c) kernel =
  fun f g ->
  {
    dom = f.dom;
    cod = g.cod;
    kern =
      (fun x ->
        { support = g.cod;
          prb =
            (fun z ->
              List.fold_left (fun acc y ->
                  acc +. ((f.kern x).prb y) *. ((g.kern y).prb z)
                ) 0.0 f.cod
            )
        }
      )
  }
    
(* Computes the pushforward, i.e. image measure, through a kernel *)
let pushforward : 'a 'b. 'a prob -> ('a, 'b) kernel -> 'b prob =
  fun prob kernel ->
  (* let domdim = Array.length prob in *)
  {
    support = kernel.cod;
    prb =
      (fun y ->
        List.fold_left
          (fun acc x ->
            let pi = prob.prb x in
            let ki = (kernel.kern x).prb y in
            acc +. pi *. ki
          ) 0.0 kernel.dom)
  }

(* Bayesian inversion. Given a probability $prior$ on 'a and a kernel $likelihood$ from 'a to 'b,
 * yields a kernel (the $posterior$) from 'b to 'a and the pushforward of the
 * $prior$ through the $likelihood$.
 *)
let inversion :
      'a 'b.
      'a prob ->           (* prior *)
      ('a ,'b) kernel ->   (* likelihood *)
      ('b, 'a) kernel * 'b prob =
  fun prior ({ dom; cod; kern } as likelihood) ->
  let nu = pushforward prior likelihood in
  let kern = fun d ->
    {
      support = dom;
      prb = fun h ->
            let ph = prior.prb h in
            (* if ph < eps then 0.0 *)
            (* else *)
              ((likelihood.kern h).prb d) *.  ph /. (nu.prb d)
    }
  in
  let posterior =
    {
      dom  = cod;
      cod  = dom;
      kern = kern;
    }
  in
  (posterior, nu)

(* We have an initial prior, a likelihood, and we just observed a data. 
 * [learn] will update the prior using Bayesian inversion. *)    
let learn :
      'a prob ->          (* prior *)
      ('a, 'b) kernel ->  (* likelihood *)
      'b ->               (* observed data *)
      'a prob =           (* outcome *)
  fun prior likelihood data ->
  let posterior, marginal = inversion prior likelihood in
  posterior.kern data

(* Same as learn but iterated on a multiset of data. *)
let learn_iter : 'a prob -> ('a, 'b) kernel -> 'b list -> 'a prob =
  fun prior likelihood data ->
  List.fold_left
    (fun prior d ->
      learn prior likelihood d
    ) prior data

(* ------------------------------------------------------------------- *)
(* An example: guessing a biased coin *)

(* a coin falls on either tails (T) or heads (H) *)    
type coin =
  | T | H

(* We have two hypotheses about the unknown coin: it is either fair or skewed. *)          
type hypothesis =
  | Fair
  | Skewed

(* Our space of data is the following two element set. *)
let dataset = [T; H]

(* Our space of hypotheses. *)                
let hypset = [Fair; Skewed]

(* A fair coin. This is a probability over [dataset]. *)
let unif =
  {
    support = dataset;
    prb =
      function
      | T -> 0.5
      | H -> 0.5
  }

(* A skewed coin. Falls mostly on heads. *)
let skewed =
  {
    support = dataset;
    prb =
      function
      | T -> 0.001
      | H -> (1.0 -. 0.001)
  }

(* A prior that believes strongly that the coin is fair. *)    
let bet_on_unif =
  {
    support = hypset;
    prb =
      function
      | Fair   -> 0.99
      | Skewed -> 0.01
  }    

(* A prior that believes strongly that the coin is skewed. *)    
let bet_on_skewed =
  {
    support = hypset;
    prb =
      function
      | Fair   -> 0.01
      | Skewed -> 0.99
  }

(* A prior that is uniform over hypotheses: with 0.5 probability, the coin is fair,
 * with 0.5 prob, the coin is skewed. *)    
let uniform_prior =
  {
    support = hypset;
    prb =
      function
      | Fair   -> 0.5
      | Skewed -> 0.5
  }

(* Our model of the unknown coin. This is a kernel from [hypset] to [dataset].
 * It associates to the "Fair" hypothesis a fair coin, and to the "Skewed" hypothesis
 * a particular skewed coin. *)
let likelihood =
  {
    dom = hypset;
    cod = dataset;
    kern = function
           | Fair   -> unif
           | Skewed -> skewed
  }

(* The truth happens to be the skewed coin. *)    
let truth = skewed

(* We sample 10 data points from the truth. *)              
let data = iid truth 10

let print_hyp = function
  | Fair   -> "Fair"
  | Skewed -> "Skewed"

let print_data = function
  | T -> "T"
  | H -> "H"

(* This is just a correctness test for our code. Pushforwarding the prior through
 * the likelihood and then through the posterior should be the identity. *)
(*           
let test =
  let prior        = bet_on_unif in
  let posterior, _ = inversion prior likelihood in
  let composed     = kleisli likelihood posterior in
  (print_prob print_hyp (pushforward prior composed))
*)
           
(* Let's put our stuff in action. We learn from [data], starting from the
 * prior that the true coin is fair, whereas it is skewed. We print the
 * updated prior. *) 
let outcome = learn_iter bet_on_unif likelihood data

let _ =
  Printf.printf "we started with the prior %s and ended up with the prior %s.\n"
                (print_prob print_hyp bet_on_unif) (print_prob print_hyp outcome)

  
