theory Regular      
  imports Words
begin

(* Regular Languages *) 
type_synonym 'a RegLang = "'a word set"

primrec pow:: "'a RegLang \<Rightarrow> nat \<Rightarrow> 'a RegLang" 
  where
   "pow s 0 = {Epsilon}"|
   "pow s (Suc n) = {u*v |u v. u:s & v:(pow s n)}"

definition quotient:: "'a RegLang \<Rightarrow> 'a \<Rightarrow> 'a RegLang"
  where
  "quotient R a = {w |w. (a . w) \<in> R}"


definition concat :: "'a RegLang \<Rightarrow> 'a word set \<Rightarrow> 'a word set" where "concat R S = {u*v |u v. u:R & v:S}"

lemma concat_containment: "a \<in> A \<and> b \<in> B \<Longrightarrow> (a * b) \<in> (concat A B)"
  apply(auto simp add: concat_def)
  done


lemma concat_epsilon: "Epsilon \<in> (concat A B) \<Longrightarrow> Epsilon \<in> A \<and> Epsilon \<in> B"
  apply(auto simp add: concat_def epsi_concat)
  done


(* Regulars *)
datatype 'a regex = None | Const "'a word" | Union "'a regex" "'a regex" | Concat "'a regex" "'a regex"  | Star "'a regex" 


lemma pow_neutral: "Epsilon \<in> pow s 0"
  apply(auto)
  done

primrec lang:: "'a regex \<Rightarrow> 'a word set" 
  where
   "lang None = {}"|
   "lang (Const w) = {w}" |
   "lang (Union r1 r2) = (lang r1) Un (lang r2)" |
   "lang (Concat r1 r2) = concat (lang r1) (lang r2)"|
   "lang (Star r) = (\<Union>n. pow (lang r) n)"

(* Epsilon is always in the Kleene closure of a regular expression *)
lemma epsi_in_star: "Epsilon \<in> lang (Star r)"
proof - 
  have "Epsilon \<in> (pow (lang  r) 0)" by (simp add: pow_neutral)
  hence "EX n. Epsilon \<in> (pow (lang  r) n)" by (rule exI)
  hence "Epsilon \<in> (\<Union>n. pow (lang  r) n)" by simp
  thus "Epsilon \<in> lang (Star r)" by simp
qed

(* A language is nullable if it accepts the empty word*)
primrec nullable:: "'a regex \<Rightarrow> bool" 
  where
  "nullable None = False" |
  "nullable (Const w) = (w = Epsilon)" |
  "nullable (Union r1 r2) = ((nullable r1) \<or> (nullable r2))" |
  "nullable (Concat r1 r2) = ((nullable r1) \<and> (nullable r2))" |
  "nullable (Star r) = True"

  
(* Show a regular expression is nullablle iff epsilon is the language *)
lemma nullability: "nullable r \<longleftrightarrow> Epsilon \<in> (lang r)"
  apply(rule)
  subgoal proof (induct r)
    case None
    then show ?case by auto
  next
    case (Const x)
    then show ?case by auto
  next
    case (Union r1 r2)
    then show ?case by auto
  next
    case (Concat r1 r2)
    then have "Epsilon \<in> (lang r1) \<and> Epsilon \<in> (lang r2)" by simp
    then have "(Epsilon * Epsilon) \<in> (concat (lang r1) (lang r2))" by (simp only: concat_containment)
    then show ?case by auto
  next
    case (Star r)
    then show ?case by (simp only: epsi_in_star)
  qed
  subgoal proof (induct r) (* Epsilon \<in> (lang r) \<longrightarrow> nullable (Star r) *)
    case None
    then have "False" by (simp add: lang_def)
    then show ?case by rule
  next
    case (Const x)
    then show ?case by simp
  next
    case IH:(Union r1 r2)
    then have "Epsilon \<in> (lang r1) \<or> Epsilon \<in> (lang r2)" by simp
    then have "(nullable r1) \<or> (nullable r2)" by (auto simp only: IH)
    then show ?case by (auto)
  next
    case IH:(Concat r1 r2)
    then have "Epsilon \<in> lang (Concat r1 r2)" by simp
    then have "Epsilon \<in> concat (lang r1) (lang r2)" by simp
    then have "Epsilon \<in> (lang r1) \<and> Epsilon \<in> (lang r2)" by (simp only: concat_epsilon)
    then show ?case using IH by (simp add: nullable_def IH)
  next
    case (Star r)
    then show ?case by (simp add: nullable_def)
  qed
done
   


(* Define derivatives of regular languages *)

primrec deriv :: "'a \<Rightarrow> 'a regex \<Rightarrow> 'a regex" 
  where
  "deriv c None = None" |
  "deriv c (Const w) = (if (at w 0) = (Some c) then (Const (fac w 1 (size w))) else None)" |
  "deriv c (Union r1 r2) = Union (deriv c r1) (deriv c r2)" |
  "deriv c (Concat r1 r2) = (if nullable r1 then Union (Concat (deriv c r1) r2) (deriv c r2) else (Concat (deriv c r1) r2))" |
  "deriv c (Star r) = Concat (deriv c r) (Star r)"


(* Lifting derivatives to words *)
primrec deriv_word:: "'a word \<Rightarrow> 'a regex \<Rightarrow> 'a regex"
  where
  "deriv_word Epsilon r = r" |
  "deriv_word (a . u) r = deriv_word u (deriv a r)"


lemma derivative_correct: "w \<in> lang (deriv a r) \<longleftrightarrow> (a . w) \<in> lang r"
  sorry



theorem "nullable (deriv_word w r) \<Longrightarrow> w \<in> (lang r)"
proof (induction w arbitrary: r)
  case Epsilon
  then have "nullable (deriv_word Epsilon r)" by simp
  then have "nullable r" by simp
  then show ?case by (simp add: nullability)
next
  case IH:(Con a w)
  then have "nullable (deriv_word (a . w)  r)" by simp
  then have "nullable (deriv_word w (deriv a r))" by simp
  with IH have "w \<in> lang (deriv a r)" by auto
  then show ?case by (simp add: derivative_correct)
qed
  
theorem "w \<in> (lang r) \<Longrightarrow> nullable (deriv_word w r)"
proof (induction w arbitrary: r)
  case Epsilon
  then show ?case by (simp add: nullability)
next
  case IH:(Con a w)
  then have "w \<in> lang (deriv a r)" by (simp add: derivative_correct)
  then show ?case using IH by simp
qed


(* Define containment a nullability of derivative *)
abbreviation contains:: "'a word \<Rightarrow> 'a regex \<Rightarrow> bool"  (infixr "\<in>" 100) where "contains w r \<equiv> nullable (deriv_word w r)" 




end