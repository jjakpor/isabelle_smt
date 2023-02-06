theory RegEx     
  imports Regular
begin

(* Regular Expressions *)
datatype 'a regex = None | Const "'a word" ("[_]") 
  | Union "'a regex" "'a regex" (infix "|" 99) 
  | Concat "'a regex" "'a regex" (infix "." 100)  
  | Star "'a regex" ("_*" 200) 
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
"lang (Star r) = star (lang r)" 
   

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
  "nullable (Star r) = True" 

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
"vu Any = None"


fun re_union::"'a regex \<Rightarrow> 'a regex \<Rightarrow> 'a regex" where 
"re_union r None = r"|
"re_union None r = r"|
"re_union r e = Union r e"

lemma re_union_correct:"(lang (re_union r e)) = (lang (Union r e))"
  apply(cases \<open>(r, e)\<close> rule: re_union.cases)
  by (auto)

fun re_concat:: "'a regex \<Rightarrow> 'a regex \<Rightarrow> 'a regex" where
"re_concat r (Const \<epsilon>) = r"|
"re_concat (Const \<epsilon>) r = r"|
"re_concat None r = None"|
"re_concat r None = None"|
"re_concat r e = Concat r e"

lemma re_concat_correct:"(lang (re_concat r e)) = (lang (Concat r e))"
  apply(cases \<open>(r, e)\<close> rule: re_concat.cases)
  by (auto simp add: concat_def)

fun re_star:: "'a regex \<Rightarrow> 'a regex" where
"re_star (Const \<epsilon>) = (Const \<epsilon>)"|
"re_star None = (Const \<epsilon>)"|
"re_star r = Star r"

lemma re_star_correct:"(lang (re_star r)) = (lang (Star r))"
  apply(cases r rule: re_star.cases)
  by (auto simp add: star_of_epsilon star_of_empty)
  

definition re_plus::"'a regex \<Rightarrow> 'a regex" where "re_plus r \<equiv> re_concat r (re_star r)"


(* Derivatives of regular languages *)
fun rderiv :: "'a \<Rightarrow> 'a regex \<Rightarrow> 'a regex" where
"rderiv c None = None" |
"rderiv c Any = (Const Epsilon)"|
"rderiv c (Const (a#w)) = (if a = c then (Const w) else None)" |
"rderiv c (Const \<epsilon>) = None"|
"rderiv c (Union r1 r2) = re_union (rderiv c r1) (rderiv c r2)" |
"rderiv c (Concat r1 r2) = (re_union (re_concat (rderiv c r1) r2)  (re_concat (vu r1) (rderiv c r2)))" |
"rderiv c (Star r) = re_concat (rderiv c r) (re_star r)"



lemma vu_null_iff: "lang (vu r) = null (lang r)"
  apply(induct r)
   apply (simp_all add: Regular.null_def)
   apply (simp add: Regular.concat_def)
  done


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
  then show ?case by (simp add: deriv_union re_union_correct)
next
  case (Concat r1 r2)
  then show ?case  by (simp add: deriv_concat vu_null_iff re_concat_correct re_union_correct)
next
  case (Star r)
  then show ?case by (simp add: deriv_star re_star_correct re_union_correct re_concat_correct)
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

theorem derivative_correctness: "w \<in> (lang r) \<longleftrightarrow> nullable (rderivw w r)"
  by (auto simp add: contains_derivw_nullable derivw_nullable_contains)

  

(* Define containment a nullability of derivative *)
definition re_contains:: "'a word \<Rightarrow> 'a regex \<Rightarrow> bool" where "re_contains w r \<equiv> nullable (rderivw w r)"

end