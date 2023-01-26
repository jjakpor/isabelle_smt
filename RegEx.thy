theory RegEx     
  imports Regular
begin

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
  

(* abbreviation vu:: "'a regex \<Rightarrow> 'a regex" where "vu r \<equiv> (if (nullable r) then (Const Epsilon) else None)" *)

primrec vu:: "'a regex \<Rightarrow> 'a regex" where
  "vu (Const w) = (if w = Epsilon then (Const w) else None)" |
  "vu None = None" |
  "vu (Union r1 r2) = Union (vu r1) (vu r2)" |
  "vu (Concat r1 r2) = Concat (vu r1) (vu r2)" |
  "vu (Star r) = (Const Epsilon)"

(* Derivatives of regular languages *)

primrec rderiv :: "'a \<Rightarrow> 'a regex \<Rightarrow> 'a regex" 
  where
  "rderiv c None = None" |
  "rderiv c (Const w) = (case w of (a . w) \<Rightarrow> if a = c then (Const w) else None | _ \<Rightarrow> None)" |
  "rderiv c (Union r1 r2) = Union (rderiv c r1) (rderiv c r2)" |
  "rderiv c (Concat r1 r2) = (Concat (rderiv c r1) r2) | (Concat (vu r1) (rderiv c r2))" |
  "rderiv c (Star r) = Concat (rderiv c r) (Star r)"



lemma vu_null_iff: "lang (vu r) = null (lang r)"
proof (induct r)
  case None
  then show ?case by (simp add: null_def)
next
  case (Const x)
  then show ?case by (simp add: null_def)
next
  case (Union r1 r2)
  then show ?case by (simp add: null_def)
next
  case IH:(Concat r1 r2)
  then have "lang (vu (Concat r1 r2)) = concat (null (lang r1)) (null (lang r2))" using IH by simp
  also have "... = (if Epsilon \<in> (lang (Concat r1 r2)) then {Epsilon} else {})" by (simp add: null_def concat_def epsi_concat)
  finally show ?case by (simp add: null_def concat_def)
next
  case (Star r1)
  then show ?case by (simp add: null_def)
qed

lemma rderiv_correct: "lang (rderiv a r) = deriv a (lang r)"
proof (induction r arbitrary: a)
  case None
  then show ?case by (simp add: deriv_empty)
next
  case (Const x)
  then show ?case proof(cases x)
    case c:Epsilon
    then have "lang (rderiv a (Const x)) = lang (rderiv a (Const Epsilon))" by simp
    also have "... = lang (None)" by (simp add: rderiv_def)
    also have "... = {}" by simp
    also have "... = deriv a (lang (Const Epsilon))" by (simp add: deriv_def)
    finally show ?thesis by (simp add: c)
  next
    case c:(Con b w)
    then have "lang (rderiv a (Const x)) = lang (rderiv a (Const (b . w)))" by simp
    then have "(a = b \<and> lang (rderiv a (Const (b . w))) = lang (Const w)) \<or> (a \<noteq> b \<and> lang (rderiv a (Const (b . w))) = lang None)" by simp
    then show ?thesis proof
      assume "(a = b \<and> lang (rderiv a (Const (b . w))) = lang (Const w))"
      then show ?thesis by (simp add: c deriv_const)
    next
      assume "(a \<noteq> b \<and> lang (rderiv a (Const (b . w))) = lang None)"
      then show ?thesis by (simp add: c deriv_const)
    qed
  qed
next
  case (Union r1 r2)
  then show ?case by (simp add: deriv_union)
next
  case IH:(Concat r1 r2)
  then have "lang (rderiv a (Concat r1 r2)) = lang ((Concat (rderiv a r1) r2) | (Concat (vu r1) (rderiv a r2)))" by simp
  also have "... = lang ((Concat (rderiv a r1) r2)) \<union> lang  (Concat (vu r1) (rderiv a r2))" by simp
  also have "... = concat (lang (rderiv a r1)) (lang r2) \<union> concat (lang (vu r1)) (lang (rderiv a r2))" by simp
  also have "... = concat (deriv a (lang r1)) (lang r2) \<union> concat (lang (vu r1)) (deriv a (lang r2))" by (simp only: IH)
  also have "... = concat (deriv a (lang r1)) (lang r2) \<union> concat (null (lang r1)) (deriv a (lang r2))" by (simp only: vu_null_iff)
  also have "... = deriv a (lang (Concat r1 r2))" by (auto simp add: deriv_concat)
  finally show ?case by simp
next
  case IH:(Star r)
  then have "lang (rderiv a (Star r)) =  lang (Concat (rderiv a r) (Star r))" by simp
  also have "... = concat (lang (rderiv a r)) (lang (Star r))" by (simp)
  also have "... = concat (lang (rderiv a r)) (star (lang r))" by (simp)
  also with IH have "... = concat (deriv a (lang r)) (star (lang r))" by (simp)
  then show ?case by (simp add: deriv_star)
qed


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
  then have "nullable (rderivw w (rderiv a r))" by (simp add: rderivw_def)
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