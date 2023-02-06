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
   



  

lemma union_none: "lang (Union None E) = lang E"
  apply(auto)
  done

lemma union_commutative: "lang (Union E R) = lang (Union R E)"
  apply(auto)
  done





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


lemma derivw_nullable_contains:"nullable (rderivw w r) \<Longrightarrow> w \<in> (lang r)"
  apply(induct w arbitrary: r)
   apply(auto simp add: nullability)
  apply (metis deriv_correct rderiv_correct)
  done

  
lemma contains_derivw_nullable:"w \<in> (lang r) \<Longrightarrow> nullable (rderivw w r)"
  apply(induct w arbitrary: r)
   apply(auto simp add: nullability)
  apply (metis deriv_correct rderiv_correct )
  done

theorem derivw_nullable_iff_contained: "w \<in> (lang r) \<longleftrightarrow> nullable (rderivw w r)"
  by (auto simp add: contains_derivw_nullable derivw_nullable_contains)


(* Normalization of Regex *)

fun normalize:: "'a regex \<Rightarrow> 'a regex" where
"normalize (Concat (Const Epsilon) R) = normalize R"|
"normalize (Concat regex.None R) = None"|
"normalize (Concat R E) = Concat (normalize R) (normalize E)"|
"normalize (Union None  R) = normalize R"|
"normalize (Union R None) = normalize R"|
"normalize (Union R E) = Union (normalize R) (normalize E)"|
"normalize (Star (Const Epsilon)) = (Const Epsilon)"|
"normalize (Star E) = Star (normalize E)"|
"normalize (Plus (Const Epsilon)) =(Const Epsilon)"|
"normalize (Plus E) = Plus (normalize E)"|
"normalize r = r"



theorem normalization_correct:"(lang (normalize r)) = (lang r)"
  sorry

abbreviation rderiv_normalize::"'a \<Rightarrow> 'a regex \<Rightarrow> 'a regex" where "rderiv_normalize c R \<equiv> normalize (rderiv c R)" 

primrec rderivw_normalize:: "'a word \<Rightarrow> 'a regex \<Rightarrow> 'a regex"
  where
  "rderivw_normalize Epsilon r = normalize r" |
  "rderivw_normalize (a#u) r = rderivw_normalize u (normalize (rderiv a r))"

lemma norm_derivw_nullable_contains:"nullable (rderivw_normalize w r) \<Longrightarrow> w \<in> (lang r)"
  apply(induct w arbitrary: r)
   apply(auto simp add: nullability)
   apply (simp add: normalization_correct)
  by (metis deriv_correct normalization_correct rderiv_correct)
  
lemma contains_norm_derivw_nullable:"w \<in> (lang r) \<Longrightarrow> nullable (rderivw_normalize w r)"
  apply(induct w arbitrary: r)
   apply(auto simp add: nullability)
  by (simp_all add: deriv_correct normalization_correct rderiv_correct)+
  


theorem norm_derivw_nullable_iff_contained: "w \<in> (lang r) \<longleftrightarrow> nullable (rderivw_normalize w r)"
  apply (auto simp add: contains_norm_derivw_nullable norm_derivw_nullable_contains)
  done
  
  

(* Define containment a nullability of derivative *)
definition re_contains:: "'a word \<Rightarrow> 'a regex \<Rightarrow> bool" where "re_contains w r \<equiv> nullable (rderivw_normalize w r)"

end