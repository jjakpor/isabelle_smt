theory Regular      
  imports Words
begin

(* Regular Languages *) 
type_synonym 'a RegLang = "'a word set"


(* Regular Operations *)
definition concat :: "'a RegLang \<Rightarrow> 'a RegLang \<Rightarrow> 'a RegLang" where "concat R S = {u*v |u v. u:R & v:S}"

primrec pow:: "'a RegLang \<Rightarrow> nat \<Rightarrow> 'a RegLang" 
  where
   "pow s 0 = {Epsilon}"|
   "pow s (Suc n) = {u*v |u v. u:s & v:(pow s n)}"

definition star :: "'a RegLang \<Rightarrow> 'a RegLang" where "star R = {w |w n. w \<in> (pow R n)}"

lemma concat_containment: "a \<in> A \<and> b \<in> B \<Longrightarrow> (a * b) \<in> (concat A B)"
  apply(auto simp add: concat_def)
  done

lemma epsilon_concat_iff: "Epsilon \<in> A \<and> Epsilon \<in> B \<longleftrightarrow> Epsilon \<in> (concat A B)"
  apply(auto simp add: concat_def)
  done

lemma epsilon_in_const_iff: "Epsilon \<in> {x} \<longleftrightarrow> x = Epsilon"
   apply(auto)
  done

lemma epsilon_in_star[simp]: "Epsilon \<in> star R"
  apply(auto simp add: star_def)
proof -
  have "Epsilon \<in> pow R 0" by simp
  then show "EX n. Epsilon \<in> pow R n" by (rule exI)
qed

(* Derivative of regular languages *)
definition deriv:: "'a \<Rightarrow> 'a RegLang \<Rightarrow> 'a RegLang" where  "deriv a R = {v |v. (a . v) \<in> R}" 

primrec derivw:: "'a word \<Rightarrow> 'a RegLang \<Rightarrow> 'a RegLang" where
  "derivw Epsilon R = R" |
  "derivw (a . w) R = derivw w (deriv a R)"

lemma deriv_empty[simp]:"deriv a {} = {}"
  apply(simp add: deriv_def)
  done
 
lemma deriv_const[simp]:"deriv a {(b . w)} = (if a = b then {w} else {})"
  apply(auto simp add: deriv_def)
  done

lemma deriv_union[simp]: "deriv a (l1 \<union> l2) = (deriv a l1) \<union> (deriv a l2)"
  apply(auto simp add: deriv_def)
  done


lemma deriv_concat[simp]:"deriv a (concat L R) = (concat (deriv a L) R) \<union> (if Epsilon \<in> L then (deriv a R) else {})"
  unfolding deriv_def concat_def
  apply(auto simp add: eq_prefix_equals)
  done

theorem deriv_correct:"w \<in> deriv a R \<longleftrightarrow> (a . w) \<in> R"
  apply(auto simp add: deriv_def)
  done


(* Regular Expressions *)
datatype 'a regex = None | Const "'a word" ("[_]") 
  | Union "'a regex" "'a regex" (infix "|" 99) 
  | Concat "'a regex" "'a regex" (infix "." 100)  
  | Star "'a regex" ("_*" 200) 


lemma pow_neutral: "Epsilon \<in> pow s 0"
  apply(auto)
  done

primrec lang:: "'a regex \<Rightarrow> 'a word set" 
  where
   "lang None = {}"|
   "lang (Const w) = {w}" |
   "lang (Union r1 r2) = (lang r1) Un (lang r2)" |
   "lang (Concat r1 r2) = concat (lang r1) (lang r2)"|
   "lang (Star r) = star (lang r)"



(* A language is nullable if it accepts the empty word*)
primrec nullable:: "'a regex \<Rightarrow> bool" 
  where
  "nullable None = False" |
  "nullable (Const w) = (w = Epsilon)" |
  "nullable (Union r1 r2) = ((nullable r1) \<or> (nullable r2))" |
  "nullable (Concat r1 r2) = ((nullable r1) \<and> (nullable r2))" |
  "nullable (Star r) = True"


lemma nullability: "nullable r \<longleftrightarrow> Epsilon \<in> (lang r)"
  apply (induct r) 
      apply(auto simp add: concat_def)
  done
  

(* Derivatives of regular languages *)

primrec rderiv :: "'a \<Rightarrow> 'a regex \<Rightarrow> 'a regex" 
  where
  "rderiv c None = None" |
  "rderiv c (Const w) = (case w of (a . w) \<Rightarrow> if a = c then (Const w) else None | _ \<Rightarrow> None)" |
  "rderiv c (Union r1 r2) = Union (rderiv c r1) (rderiv c r2)" |
  "rderiv c (Concat r1 r2) = (if nullable r1 then Union (Concat (rderiv c r1) r2) (rderiv c r2) else (Concat (rderiv c r1) r2))" |
  "rderiv c (Star r) = Concat (rderiv c r) (Star r)"


lemma rderiv_correct: "lang (rderiv a r) = deriv a (lang r)"
  apply(induct r)
  apply(auto)
  sorry

primrec rderivw:: "'a word \<Rightarrow> 'a regex \<Rightarrow> 'a regex"
  where
  "rderivw Epsilon r = r" |
  "rderivw (a . u) r = rderivw u (rderiv a r)"


theorem "nullable (rderivw w r) \<Longrightarrow> w \<in> (lang r)"
proof (induction w arbitrary: r)
  case Epsilon
  then have "nullable (rderivw Epsilon r)" by simp
  then have "nullable r" by simp
  then show ?case by (simp add: nullability)
next
  case IH:(Con a w)
  then have "nullable (rderivw (a . w)  r)" by simp
  then have "nullable (rderivw w (rderiv a r))" by simp
  with IH have "w \<in> lang (rderiv a r)" by auto
  then have "(a . w) \<in> (lang r)" by (simp add: rderiv_correct deriv_correct)
  then show ?case by (auto)
qed
  
theorem "w \<in> (lang r) \<Longrightarrow> nullable (rderivw w r)"
proof (induction w arbitrary: r)
  case Epsilon
  then show ?case by (simp add: nullability)
next
  case IH:(Con a w)
  then have "(a . w) \<in> (lang r)" by simp
  then have "w \<in> deriv a (lang r)" by (simp add: deriv_correct)
  then have "w \<in> lang (rderiv a r)" by (simp add: rderiv_correct)
  then show ?case using IH by simp
qed

(* Define containment a nullability of derivative *)
abbreviation contains:: "'a word \<Rightarrow> 'a regex \<Rightarrow> bool"  (infixr "\<in>" 100) where "contains w r \<equiv> nullable (rderivw w r)" 


end