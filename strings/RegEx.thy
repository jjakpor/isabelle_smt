theory RegEx     
  imports Regular
begin

(* Regular Expressions *)
datatype 'a regex = None | Const "'a word" ("[_]") 
  | Union "'a regex" "'a regex" (infix "|" 99) 
  | Concat "'a regex" "'a regex" (infix "." 100)  
  | Star "'a regex" ("_*" 200) 
  | Plus "'a regex"
  | Any


lemma pow_neutral: "Epsilon \<in> pow s 0"
  apply(auto)
  done


primrec lang:: "'a regex \<Rightarrow> 'a word set"  where
"lang None = {}"|
"lang Any = {v. EX a. v=a#\<epsilon>}" | 
"lang (Const w) = {w}" |
"lang (Union r1 r2) = (lang r1) Un (lang r2)" |
"lang (Concat r1 r2) = concat (lang r1) (lang r2)"|
"lang (Star r) = star (lang r)" |
"lang (Plus r) = concat (lang r) (star (lang r))"
   


fun re_simp:: "'a regex \<Rightarrow> 'a regex" where
"re_simp (Concat (Const Epsilon) R) = re_simp R"|
"re_simp (Concat regex.None R) = None"|
"re_simp (Concat R E) = Concat (re_simp R) (re_simp E)"|
"re_simp (Union None  R) = re_simp R"|
"re_simp (Union R None) = re_simp R"|
"re_simp (Union R E) = Union (re_simp R) (re_simp E)"|
"re_simp (Star (Const Epsilon)) = (Const Epsilon)"|
"re_simp (Star E) = Star (re_simp E)"|
"re_simp (Plus (Const Epsilon)) =(Const Epsilon)"|
"re_simp (Plus E) = Plus (re_simp E)"|
"re_simp r = r"
  

lemma union_none: "lang (Union None E) = lang E"
  apply(auto)
  done

lemma union_commutative: "lang (Union E R) = lang (Union R E)"
  apply(auto)
  done

theorem simps_correct:"(lang (re_simp r)) = (lang r)"
  apply(induct r)
      apply(simp_all)
     apply(cases)
  apply(auto)
  sorry
  



(* A language is nullable if it accepts the empty word*)
primrec nullable:: "'a regex \<Rightarrow> bool" 
  where
  "nullable None = False" |
  "nullable Any = False" |
  "nullable (Const w) = (w = Epsilon)" |
  "nullable (Union r1 r2) = ((nullable r1) \<or> (nullable r2))" |
  "nullable (Concat r1 r2) = ((nullable r1) \<and> (nullable r2))" |
  "nullable (Star r) = True" |
  "nullable (Plus r) = nullable r"

lemma nullability: "nullable r \<longleftrightarrow> Epsilon \<in> (lang r)"
  apply (induct r) 
  apply(auto simp add: concat_def)
  done
  

(* abbreviation vu:: "'a regex \<Rightarrow> 'a regex" where "vu r \<equiv> (if (nullable r) then (Const Epsilon) else None)" *)

primrec vu:: "'a regex \<Rightarrow> 'a regex" where
"vu (Const w) = (if w = Epsilon then (Const w) else None)" |
"vu None = None" |
"vu (Union r1 r2) = Union (vu r1) (vu r2)" |
"vu (Concat r1 r2) = Concat (vu r1) (vu r2)" |
"vu (Star r) = (Const Epsilon)" |
"vu (Plus r) = vu r"|
"vu Any = None"

 

(* Derivatives of regular languages *)
fun rderiv :: "'a \<Rightarrow> 'a regex \<Rightarrow> 'a regex" where
"rderiv c None = None" |
"rderiv c Any = (Const Epsilon)"|
"rderiv c (Const (a#w)) = (if a = c then (Const w) else None)" |
"rderiv c (Const \<epsilon>) = None"|
"rderiv c (Union r1 r2) = Union (rderiv c r1) (rderiv c r2)" |
"rderiv c (Concat r1 r2) = (Union (Concat (rderiv c r1) r2)  (Concat (vu r1) (rderiv c r2)))" |
"rderiv c (Star r) = Concat (rderiv c r) (Star r)"|
"rderiv c (Plus r) = Concat (rderiv c r) (Star r)"


abbreviation simp_rderiv::"'a \<Rightarrow> 'a regex \<Rightarrow> 'a regex" where "simp_rderiv c R \<equiv> re_simp (rderiv c R)" 

lemma vu_null_iff: "lang (vu r) = null (lang r)"
  apply(induct r)
   apply (simp_all add: Regular.null_def)
   apply (simp add: Regular.concat_def)
  using epsilon_concat_iff by fastforce


lemma rderiv_correct: "lang (rderiv a r) = deriv a (lang r)"
proof(induction r arbitrary: a)
  case None
  then show ?case by (simp add: deriv_empty)
next
  case (Const x)  
  then show ?case proof(cases x)
    case Nil
    then show ?thesis by (simp add: deriv_def)
  next
    case (Cons a list)
    then show ?thesis by (simp add: deriv_const)
    qed
next
  case (Union r1 r2)
  then show ?case by (simp add: deriv_union)
next
  case (Concat r1 r2)
  then show ?case  by (simp add: deriv_concat vu_null_iff)
next
  case (Star r)
  then show ?case by (simp add: deriv_star)
next
  case (Plus r)
  then show ?case by (metis deriv_concat deriv_star deriv_union inf_sup_aci(5) lang.simps(5) lang.simps(6) lang.simps(7) rderiv.simps(8) star_unroll sup.right_idem)
next
  case Any
  then show ?case by (auto simp add: deriv_def)
qed



primrec rderivw:: "'a word \<Rightarrow> 'a regex \<Rightarrow> 'a regex"
  where
  "rderivw Epsilon r = r" |
  "rderivw (a#u) r = rderivw u (rderiv a r)"

primrec simp_rderivw:: "'a word \<Rightarrow> 'a regex \<Rightarrow> 'a regex"
  where
  "simp_rderivw Epsilon r = re_simp r" |
  "simp_rderivw (a#u) r = simp_rderivw u (re_simp (rderiv a r))"


theorem "lang (simp_rderiv w R) = lang (rderiv w R)"
  apply (simp add: simps_correct)
  done

theorem "nullable (rderivw w r) \<Longrightarrow> w \<in> (lang r)"
  apply(induct w arbitrary: r)
   apply(auto simp add: nullability)
  apply (metis deriv_correct rderiv_correct)
  done

  
theorem "w \<in> (lang r) \<Longrightarrow> nullable (rderivw w r)"
  apply(induct w arbitrary: r)
   apply(auto simp add: nullability)
  apply (metis deriv_correct rderiv_correct)
  done


(* Define containment a nullability of derivative *)
abbreviation contains:: "'a word \<Rightarrow> 'a regex \<Rightarrow> bool"  (infixr "\<in>" 100) where "contains w r \<equiv> nullable (simp_rderivw w r)"


end