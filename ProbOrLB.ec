(* Lower Bound Proof for Adaptive Probabilistic Or *)

prover quorum=1 ["Z3" "Alt-Ergo"].

require import AllCore Distr DBool DInterval DProd List StdOrder.
import RealOrder.

require ProbLowerBounds.

(* number of arguments to or function *)

op arity : {int | 1 <= arity} as ge1_arity.

op some_true (inps : bool list) =
  exists (i : int),
  0 <= i < arity /\ nth witness inps i = true.

op f (_ : unit, xs : bool list) =
  if size xs <> arity
  then None
  else Some (some_true xs).

type aux_query_basis = (int * bool) * unit.

op daux_query_basis : aux_query_basis distr =
  ([0 .. arity - 1] `*` {0,1}) `*` duniform [()].

op query (aqb : aux_query_basis) (qry : int) =
  if aqb \in daux_query_basis /\ 0 <= qry < arity
  then Some (if aqb.`1.`1 = qry then aqb.`1.`2 else false)
  else None.

clone import ProbLowerBounds as PLBF with
  type inp         <- bool,
  type out         <- bool,
  op arity         <- arity,
  type aux         <- unit,
  op good          <- fun _ _ => true,
  op f             <- f,
  type aux_query_basis <- aux_query_basis,
  op daux_query_basis  <- daux_query_basis,
  op query         <- query
proof *.
realize ge0_arity. smt(ge1_arity). qed.
realize good. smt(). qed.
realize bad. smt(). qed.
realize daux_query_basis_ll.
rewrite /daux_query_basis dprod_ll dprod_ll drange_ll /=.
smt(ge1_arity).
by rewrite dbool_ll duniform_ll.
qed.
realize query_in_range. smt(). qed.
realize query_out_range. smt(). qed.
realize query_good. trivial. qed.

(* see after the section for the main result *)

section.

declare module Alg <: ALG.

(* we assume Alg's procedures terminate with probability 1%r
   no matter what their arguments or current states are *)

declare axiom Alg_init_ll   : islossless Alg.init.
declare axiom Alg_query_ll  : islossless Alg.query.
declare axiom Alg_answer_ll : islossless Alg.answer.
declare axiom Alg_result_ll : islossless Alg.result.

lemma f_inputs_eq_aqb12 (aqb : aux_query_basis) :
  aqb \in daux_query_basis =>  0 <= aqb.`1.`1 < arity =>
  f () (inputs aqb) = Some (aqb.`1.`2).
proof.
move => aqb_in_basis aqb11_in_rng.
rewrite /f /inputs /query /=.
rewrite size_map size_range /=.
have -> /= : max 0 arity = arity
  by rewrite lez_maxr 1:(lez_trans 1) // ge1_arity.
case aqb.`1.`2 => _.
rewrite eqT /= /some_true.
exists aqb.`1.`1.
split; first trivial.
rewrite (nth_map witness) 1:size_range /=.
rewrite IntOrder.ler_maxr 1:(lez_trans 1) // 1:ge1_arity.
rewrite eqT aqb_in_basis /=.
smt(nth_range).
rewrite neqF /some_true negb_exists => i /=.
rewrite eqT negb_and.
case (0 <= i < arity) => [i_rng /= | //].
rewrite (nth_map witness) 1:size_range /=.
rewrite IntOrder.ler_maxr 1:(lez_trans 1) // 1:ge1_arity.
smt(nth_range).
qed.

local module G0 = {
  proc main(numq : int) : bool = {
    var i : int <- 0;
    var qry : int;
    var j : int;
    var b, b', a : bool;
    (* choose the two random parameters used to answer queries *)
    j <$ [0 .. arity - 1];
    b <$ {0,1};
    (* initialize the algorithm *)
    Alg.init((), numq);
    (* let algorithm adaptively issue its numq queries *)
    while (i < numq) {
      (* ask algorithm to issue its next query *)
      qry <@ Alg.query();
      if (qry < 0 \/ arity <= qry) {  (* qry is 0, if out of range *)
        qry <- 0;
      }
      (* give algorithm answer to its query *)
      Alg.answer(if qry = j then b else false);
      i <- i + 1;
    }
    (* ask the algorithm to predict result of or function *)
    b' <@ Alg.result();
    (* returns whether the algorithm won, i.e., correctly
       predicated the answer *)
    return b' = b;
  }
}.

local clone ProdSampling as PS1 with
  type t1 <- int * bool,
  type t2 <- unit
proof *.

local clone ProdSampling as PS2 with
  type t1 <- int,
  type t2 <- bool.

local lemma G_G0 (numq' : int) &m :
  Pr[G(Alg).main(numq') @ &m : res] = Pr[G0.main(numq') @ &m : res].
proof.
byequiv => //.
proc.
seq 3 3 :
  (={glob Alg, i, numq} /\ aqb{1}.`1.`1 = j{2} /\ aqb{1}.`1.`2 = b{2} /\
   0 <= j{2} < arity /\ aqb{1} \in daux_query_basis).
sp; wp.
transitivity{1}
  { aqb <@ PS1.S.sample([0 .. arity - 1] `*` {0,1}, duniform [()]); }
  (={glob Alg, i, numq} ==> ={glob Alg, i, numq, aqb})
  (={glob Alg, i, numq} ==>
   ={glob Alg, i, numq} /\
   aqb{1}.`1.`1 = j{2} /\ aqb{1}.`1.`2 = b{2} /\ 0 <= j{2} < arity /\
   aqb{1} \in daux_query_basis) => //.
smt().
inline*; auto.
transitivity{1}
  { aqb <@ PS1.S.sample2([0 .. arity - 1] `*` {0,1}, duniform [()]); }
  (={glob Alg, i, numq} ==> ={glob Alg, i, numq, aqb})
  (={glob Alg, i, numq} ==>
   ={glob Alg, i, numq} /\
   aqb{1}.`1.`1 = j{2} /\ aqb{1}.`1.`2 = b{2} /\ 0 <= j{2} < arity /\
   aqb{1} \in daux_query_basis) => //.
smt().
call PS1.sample_sample2; first auto.
inline; wp; rnd{1}; swap{1} 2 1; wp => /=.
conseq
  (_ :
   _ ==>
   ={glob Alg, i, numq} /\
   r1{1}.`1 = j{2} /\ r1{1}.`2 = b{2} /\ 0 <= j{2} < arity /\
   (r1{1}, ()) \in daux_query_basis).
progress; [by rewrite duniform_ll | smt()].
transitivity{1}
  { r1 <@ PS2.S.sample([0 .. arity - 1], {0,1}); }
  (={glob Alg, i, numq} ==> ={glob Alg, i, numq, r1})
  (={glob Alg, i, numq} ==>
   ={glob Alg, i, numq} /\
   r1{1}.`1 = j{2} /\ r1{1}.`2 = b{2} /\ 0 <= j{2} < arity /\
   ((r1{1}, tt) \in daux_query_basis)) => //.
smt().
inline; auto.
transitivity{1}
  { r1 <@ PS2.S.sample2([0 .. arity - 1], {0,1}); }
  (={glob Alg, i, numq} ==> ={glob Alg, i, numq, r1})
  (={glob Alg, i, numq} ==>
   ={glob Alg, i, numq} /\
   r1{1}.`1 = j{2} /\ r1{1}.`2 = b{2} /\ 0 <= j{2} < arity /\
   r1{1} \in [0 .. arity - 1] `*` {0,1}) => //.
smt().
progress.
rewrite /daux_query_basis.
rewrite 2!supp_dprod.
rewrite supp_drange.
rewrite supp_dbool.
rewrite supp_duniform.
simplify.
smt().
call PS2.sample_sample2; first auto.
inline; auto; progress.
smt(supp_dinter).
smt(supp_dinter).
rewrite supp_dprod supp_drange supp_dbool /=.
smt(supp_dinter).
conseq (_ : _ ==> out{1} = b'{2} /\ aqb{1}.`1.`2 = b{2}).
progress; congr; case (aux{1}).
by rewrite f_inputs_eq_aqb12 1:/#.
call (_ : true).
while
  (={glob Alg, i, numq} /\ aqb{1}.`1.`1 = j{2} /\
   aqb{1}.`1.`2 = b{2} /\ aqb{1} \in daux_query_basis).
wp.
call (_ : true).
wp.
call (_ : true).
auto => /> &1 &2 aqb_in_basis _ result_R.
rewrite /query /=.
split => [_ | result_R_in_rng].
have -> /= : 0 < arity by smt(ge1_arity).
rewrite aqb_in_basis /#.
have -> /= : 0 <= result_R < arity by smt().
rewrite aqb_in_basis /#.
call (_ : true); auto.
qed.

(* G1 is like G0, except instrumented to detect a bad event:
   at some stage of the loop, when b is true, algorithm queries j *)

local module G1 = {
  var bad : bool

  proc main(numq : int) : bool = {
    var i : int <- 0;
    var qry : int;
    var j : int;
    var b, b', a : bool;
    j <$ [0 .. arity - 1];
    b <$ {0,1};
    bad <- false;
    Alg.init((), numq);
    while (i < numq) {
      qry <@ Alg.query();
      if (qry < 0 \/ arity <= qry) {
        qry <- 0;
      }
      bad <- bad \/ qry = j /\ b;
      Alg.answer(if qry = j then b else false);
      i <- i + 1;
    }
    b' <@ Alg.result();
    return b' = b;
  }
}.

local lemma G0_G1 (numq' : int) &m :
  Pr[G0.main(numq') @ &m : res] = Pr[G1.main(numq') @ &m : res].
proof. byequiv => //; sim. qed.

local lemma G_G1 (numq' : int) &m :
  Pr[G(Alg).main(numq') @ &m : res] = Pr[G1.main(numq') @ &m : res].
proof. by rewrite G_G0 G0_G1. qed.

(* like G1, except all query answers are false *)

local module G2 = {
  var bad : bool

  proc main(numq: int) : bool = {
    var i : int <- 0;
    var qry : int;
    var j : int;
    var b, b', a : bool;
    j <$ [0 .. arity - 1];
    b <$ {0,1};
    bad <- false;
    Alg.init((), numq);
    while (i < numq) {
      qry <@ Alg.query();
      if (qry < 0 \/ arity <= qry) {
        qry <- 0;
      }
      bad <- bad \/ qry = j /\ b;
      Alg.answer(false);  (* note *)
      i <- i + 1;
    }
    b' <@ Alg.result();
    return b' = b;
  }
}.

(* we use up to bad reasoning, to connect G1 and G2 *)

local lemma G1_G2_equiv :
  equiv[G1.main ~ G2.main :
        ={glob Alg, numq} ==>
        ={bad}(G1, G2) /\ (! G1.bad{1} => ={res})].
proof.
proc.
seq 5 5 :
  (={i, j, b, glob Alg, numq} /\ ={bad}(G1, G2) /\
   i{1} = 0 /\ ! G1.bad{1}); first call (_ : true); auto.
call
  (_ :
   ={bad}(G1, G2) /\ (! G1.bad{1} => ={glob Alg}) ==>
   ={bad}(G1, G2) /\ (! G1.bad{1} => ={res})).
proc
  (G2.bad)
  (={bad}(G1, G2))
  (G1.bad{1}); first 2 smt().
apply Alg_result_ll.
while (={i, j, b, numq} /\ ={bad}(G1, G2) /\ (! G1.bad{1} => ={glob Alg})).
seq 2 2 :
  (={i, j, b, numq} /\ ={bad}(G1, G2) /\ (! G1.bad{1} => ={qry, glob Alg})).
wp.
call
  (_ :
   ={bad}(G1, G2) /\ (! G1.bad{1} => ={glob Alg}) ==>
   ={bad}(G1, G2) /\ (! G1.bad{1} => ={res, glob Alg})).
proc
  (G2.bad)
  (={bad}(G1, G2))
  (G1.bad{1}); first 2 smt().
apply Alg_query_ll.
auto; smt().
sp; elim* => bad_R bad_L; wp.
call
  (_ :
   ={bad}(G1, G2) /\ (! G1.bad{1} => ={inp, glob Alg}) ==>
   ={bad}(G1, G2) /\ (! G1.bad{1} => ={glob Alg})).
proc
  (G2.bad)
  (={bad}(G1, G2))
  (G1.bad{1}); first 2 smt().
apply Alg_answer_ll.
(* smt can prove that the answer is false in G1 when
   the bad event is false *)
auto; smt().
auto; smt().
qed.

(* G2' is like G2 except the while loop simply collects the queries,
   and after the loop, bad is set based on b and the relationship
   between the queries and l *)

local module G2' = {
  var bad : bool

  proc main(numq : int) : bool = {
    var i : int <- 0;
    var qry : int;
    var j : int;
    var b, b', a : bool;
    var qrys : int list <- [];
    j <$ [0 .. arity - 1];
    b <$ {0,1};
    Alg.init((), numq);
    while (i < numq) {
      qry <@ Alg.query();
      if (qry < 0 \/ arity <= qry) {
        qry <- 0;
      }
      qrys <- qrys ++ [qry];
      Alg.answer(false);
      i <- i + 1;
    }
    bad <- j \in qrys /\ b;
    b' <@ Alg.result();
    return b' = b;
  }
}.

(* G2 and G2' are equivalent in terms of whether they set the
   bad event *)

local lemma G2_G2'_bad (numq' : int) &m :
  0 <= numq' =>
  Pr[G2.main(numq') @ &m : G2.bad] = Pr[G2'.main(numq') @ &m : G2'.bad].
proof.
move => ge0_numq'.
byequiv => //.
proc.
seq 5 5 :
  (={i, j, b, glob Alg, numq} /\ i{1} = 0 /\ 0 <= numq{1} /\
   ! G2.bad{1} /\ qrys{2} = []); first call (_ : true); auto.
call (_ : true); first auto.
while
  (={i, j, b, glob Alg, numq} /\ 0 <= i{2} <= numq{1} /\ size qrys{2} = i{2} /\
   (G2.bad{1} <=> j{2} \in qrys{2} /\ b{2})).
wp.
call (_ : true).
wp.
call (_ : true).
auto; smt(size_cat mem_cat).
auto.
qed.

(* bound the probability of failure in G2' (not clear how to do
   this directly on G2) *)

lemma count_mem_uniq_le_size_of_mem (xs ys : 'a list) :
  uniq ys => count (mem xs) ys <= size xs.
proof.
move => uniq_ys.
have -> : mem xs = mem (undup xs).
  apply fun_ext => y; by rewrite mem_undup.
rewrite count_swap // 1:undup_uniq.
rewrite (lez_trans (size (undup xs))) 1:count_size size_undup.
qed.

local lemma G2'_bad (numq' : int) &m :
  0 <= numq' =>
  Pr[G2'.main(numq') @ &m : G2'.bad] <= numq'%r / (arity * 2)%r.
proof.
move => ge0_numq'.
byphoare (_ : numq = numq' ==> _) => //.
proc.
swap 7 1; wp.
swap [3..4] 3.
seq 5 :
  (size qrys = numq)
  1%r
  (numq'%r / (arity * 2)%r)
  0%r
  0%r
  (numq = numq') => //.
call (_ : true).
while (numq = numq').
wp.
call (_ : true).
wp.
call (_ : true).
auto.
call (_ : true); first auto.
seq 1 :
  (j \in qrys)
  (numq'%r / arity%r)
  (1%r / 2%r)
  1%r
  0%r
  (numq = numq') => //.
auto.
rnd; simplify.
auto; progress.
rewrite dinterE /= lez_maxr 1:(lez_trans 1) // 1:ge1_arity ler_pmul2r.
rewrite invr_gt0 lt_fromint ltzE ge1_arity.
rewrite le_fromint size_filter count_mem_uniq_le_size_of_mem range_uniq.
rewrite mulr_ge0 1:le_fromint //.
rewrite invr_ge0 le_fromint 1:(lez_trans 1) // ge1_arity.
rnd (pred1 true); simplify.
auto; progress.
rewrite dbool1E /#.
smt().
by rewrite invr_ge0 le_fromint.
hoare.
rnd.
auto => />.
smt().
hoare.
call (_ : true).
while (i <= numq /\ size qrys = i).
wp.
call (_ : true).
wp.
call (_ : true).
auto; progress.
smt().
by rewrite cats1 size_rcons.
smt().
by rewrite cats1 size_rcons.
call (_ : true).
auto; smt().
qed.

(* bound the probability of failure in G2 *)

local lemma G2_bad (numq' : int) &m :
  0 <= numq' =>
  Pr[G2.main(numq') @ &m : G2.bad] <= numq'%r / (arity * 2)%r.
proof.
move => ge0_numq'.
by rewrite (G2_G2'_bad numq' &m) // (G2'_bad numq' &m).
qed.

local lemma G1_G2 (numq' : int) &m :
  0 <= numq' =>
  `|Pr[G1.main(numq') @ &m : res] - Pr[G2.main(numq') @ &m : res]| <=
  numq'%r / (arity * 2)%r.
proof.
move => ge0_numq'.
rewrite (ler_trans Pr[G2.main(numq') @ &m : G2.bad]).
byequiv
  (_ :
   ={glob Alg, numq} ==>
   ={bad}(G1, G2) /\ (! G1.bad{1} => ={res})) :
  G1.bad => //.
apply G1_G2_equiv.
smt().
by apply (G2_bad numq' &m).
qed.

local lemma G_G2 (numq' : int) &m :
  0 <= numq' =>
  `|Pr[G(Alg).main(numq') @ &m : res] - Pr[G2.main(numq') @ &m : res]| <=
  numq'%r / (arity * 2)%r.
proof.
move => ge0_numq'.
by rewrite (G_G1 numq' &m) (G1_G2 numq' &m).
qed.

(* like G2, except bad event removed *)

local module G3 = {
  proc main(numq : int) : bool = {
    var i : int <- 0;
    var qry : int;
    var j : int;
    var b, b', a : bool;
    j <$ [0 .. arity - 1];
    b <$ {0,1};
    Alg.init((), numq);
    while (i < numq) {
      qry <@ Alg.query();
      if (qry < 0 \/ arity <= qry) {
        qry <- 0;
      }
      Alg.answer(false);
      i <- i + 1;
    }
    b' <@ Alg.result();
    return b' = b;
  }
}.

local lemma G2_G3 (numq' : int) &m :
  Pr[G2.main(numq') @ &m : res] = Pr[G3.main(numq') @ &m : res].
proof. byequiv => //; sim. qed.

local lemma G_G3 (numq' : int) &m :
  0 <= numq' =>
  `|Pr[G(Alg).main(numq') @ &m : res] - Pr[G3.main(numq') @ &m : res]| <=
  numq'%r / (arity * 2)%r.
proof.
move => ge0_numq'.
by rewrite -(G2_G3 numq' &m) (G_G2 numq' &m).
qed.

(* the algorithm wins G3 exactly half the time *)

local lemma G3_prob (numq' : int) &m :
  0 <= numq' => Pr[G3.main(numq') @ &m : res] = 1%r / 2%r.
proof.
move => ge0_numq'.
byphoare (_ : numq = numq' ==> _) => //.
proc.
swap 3 3.
swap 2 3.
rnd (pred1 b').
rnd.
call (_ : true).
apply Alg_result_ll.
while (i <= numq) (numq - i).
move => z.
wp.
call (_ : true).
apply Alg_answer_ll.
wp.
call (_ : true).
apply Alg_query_ll.
auto; smt().
call Alg_init_ll.
auto; progress.
smt().
rewrite dbool1E /#.
smt().
rewrite weight_dinter.
smt(ge1_arity).
qed.

lemma G_close_up_bound (numq' : int) &m :
  0 <= numq' =>
  `|Pr[G(Alg).main(numq') @ &m : res] - 1%r / 2%r| <=
  numq'%r / (arity * 2)%r.
proof.
move => ge0_numq'.
by rewrite -(G3_prob numq' &m) // (G_G3 numq' &m).
qed.

end section.

lemma G_close_to_half_up_bound (Alg <: ALG) (numq' : int) &m :
  islossless Alg.init => islossless Alg.query =>
  islossless Alg.answer => islossless Alg.result =>
  0 <= numq' =>
  `|Pr[G(Alg).main(numq') @ &m : res] - 1%r / 2%r| <=
  numq'%r / (arity * 2)%r.
proof.
move => Alg_init_ll Alg_query_ll Alg_answer_ll Alg_result_ll ge0_numq'.
by apply (G_close_up_bound Alg _ _ _ _ numq' &m).
qed.

lemma G_up_bound (Alg <: ALG) (numq' : int) &m :
  islossless Alg.init => islossless Alg.query =>
  islossless Alg.answer => islossless Alg.result =>
  0 <= numq' =>
  Pr[G(Alg).main(numq') @ &m : res] <=
  1%r / 2%r + numq'%r / (arity * 2)%r.
proof.
move => Alg_init_ll Alg_query_ll Alg_answer_ll Alg_result_ll ge0_numq'.
have close_bnd := G_close_to_half_up_bound Alg numq' &m _ _ _ _ => //.
have ge0_pr : 0%r <= Pr[G(Alg).main(numq') @ &m : res]
  by rewrite Pr [mu_ge0].
have ge0_half : 0%r <= 1%r / 2%r by rewrite divr_ge0.
smt().
qed.

lemma lower_bound (Alg <: ALG) (numq1 numq2 : int) &m :
  islossless Alg.init => islossless Alg.query =>
  islossless Alg.answer => islossless Alg.result =>
  0 <= numq1 => 0 <= numq2 =>
  1%r / 2%r + numq1%r / (arity * 2)%r <= Pr[G(Alg).main(numq2) @ &m : res] =>
  forall (numq : int),
  0 <= numq =>
  Pr[G(Alg).main(numq2) @ &m : res] <= Pr[G(Alg).main(numq) @ &m : res] =>
  numq1 <= numq.
proof.
move => Alg_init_ll Alg_query_ll Alg_answer_ll Alg_result_ll.
move => ge0_numq1 ge0_numq2 le_bnd_numq1_G_numq2.
apply
  (lower_bound Alg (fun nq => 1%r / 2%r + nq%r / (arity * 2)%r)
   _ _ numq1 numq2 &m) => //.
rewrite /=.
move => numq &m0 ge0_numq /=.
apply (G_up_bound Alg numq &m0 _ _ _ _) => //.
rewrite /=.
smt(ge1_arity).
qed.
