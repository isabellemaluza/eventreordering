theory JSLocality
imports JSHeapWF
begin

(* ==========================================================================
   Locality of Heap Operations
   ========================================================================== *)


(* ==========================================================================
   Helper lemmas for find/filter on association lists
   ========================================================================== *)

lemma find_filter_other_key:
  assumes IJ: "i ~= j"
  shows
    "find (%(k,v). k = i)
       (filter (%(k,_). k ~= j) h)
     =
     find (%(k,v). k = i) h"
  using IJ
proof (induct h)
  case Nil
  then show ?case
    by simp
next
  case (Cons a h)

  obtain k v where A [simp]: "a = (k,v)"
    by (cases a)

  show ?case
    using Cons.hyps IJ
    by (cases "k = i"; cases "k = j"; simp)
qed


lemma find_filter_same_key_none:
  "find (%(k,v). k = i)
     (filter (%(k,_). k ~= i) h)
   = None"
proof (induct h)
  case Nil
  then show ?case
    by simp
next
  case (Cons a h)

  obtain k v where A [simp]: "a = (k,v)"
    by (cases a)

  show ?case
    using Cons.hyps
    by (cases "k = i"; simp)
qed


(* ==========================================================================
   Basic load/write locality
   ========================================================================== *)

lemma load_object_write_same:
  "load_object i (write_object i v s) = Some v"
  unfolding load_object.simps write_object.simps
  by simp


lemma load_object_write_independent:
  assumes IJ: "i ~= j"
  shows
    "load_object i (write_object j v s) =
     load_object i s"
proof -
  have F:
    "find (%(k,v). k = i)
       (filter (%(k,_). k ~= j) (Heap_s s))
     =
     find (%(k,v). k = i) (Heap_s s)"
    using IJ
    by (rule find_filter_other_key)

  show ?thesis
    unfolding load_object.simps write_object.simps
    using IJ F
    by simp
qed


lemma load_object_remove_same:
  "load_object i (remove_object i s) = None"
proof -
  have F:
    "find (%(k,v). k = i)
       (filter (%(k,_). k ~= i) (Heap_s s))
     = None"
    by (rule find_filter_same_key_none)

  show ?thesis
    unfolding load_object.simps remove_object.simps
    using F
    by simp
qed


lemma load_object_remove_independent:
  assumes IJ: "i ~= j"
  shows
    "load_object i (remove_object j s) =
     load_object i s"
proof -
  have F:
    "find (%(k,v). k = i)
       (filter (%(k,_). k ~= j) (Heap_s s))
     =
     find (%(k,v). k = i) (Heap_s s)"
    using IJ
    by (rule find_filter_other_key)

  show ?thesis
    unfolding load_object.simps remove_object.simps
    using IJ F
    by simp
qed


(* ==========================================================================
   Extensional heap equivalence
   ========================================================================== *)

definition heap_ext_eq :: "js_state => js_state => bool" where
  "heap_ext_eq s1 s2 =
     (ALL k. load_object k s1 = load_object k s2)"


lemma heap_ext_eq_refl:
  "heap_ext_eq s s"
  unfolding heap_ext_eq_def
  by simp


lemma heap_ext_eq_sym:
  assumes E: "heap_ext_eq s1 s2"
  shows "heap_ext_eq s2 s1"
  using E
  unfolding heap_ext_eq_def
  by auto


lemma heap_ext_eq_trans:
  assumes E1: "heap_ext_eq s1 s2"
      and E2: "heap_ext_eq s2 s3"
  shows "heap_ext_eq s1 s3"
  using E1 E2
  unfolding heap_ext_eq_def
  by auto


(* ==========================================================================
   Independent writes commute extensionally
   ========================================================================== *)

lemma write_object_commute_load:
  assumes IJ: "i ~= j"
  shows
    "load_object k
       (write_object i vi
         (write_object j vj s))
     =
     load_object k
       (write_object j vj
         (write_object i vi s))"
proof (cases "k = i")
  case True

  have JI:
    "j ~= i"
    using IJ
    by simp

  show ?thesis
    using True IJ JI
    by (simp add:
        load_object_write_same
        load_object_write_independent)

next
  case KI: False

  show ?thesis
  proof (cases "k = j")
    case True

    show ?thesis
      using True KI IJ
      by (simp add:
          load_object_write_same
          load_object_write_independent)

  next
    case KJ: False

    have L1:
      "load_object k
         (write_object i vi
           (write_object j vj s))
       =
       load_object k
         (write_object j vj s)"
      using KI
      by (rule load_object_write_independent)

    have L2:
      "load_object k
         (write_object j vj s)
       =
       load_object k s"
      using KJ
      by (rule load_object_write_independent)

    have R1:
      "load_object k
         (write_object j vj
           (write_object i vi s))
       =
       load_object k
         (write_object i vi s)"
      using KJ
      by (rule load_object_write_independent)

    have R2:
      "load_object k
         (write_object i vi s)
       =
       load_object k s"
      using KI
      by (rule load_object_write_independent)

    have L:
      "load_object k
         (write_object i vi
           (write_object j vj s))
       =
       load_object k s"
      using L1 L2
      by simp

    have R:
      "load_object k
         (write_object j vj
           (write_object i vi s))
       =
       load_object k s"
      using R1 R2
      by simp

    show ?thesis
      using L R
      by simp
  qed
qed


theorem write_object_commute_ext:
  assumes IJ: "i ~= j"
  shows
    "heap_ext_eq
       (write_object i vi
         (write_object j vj s))
       (write_object j vj
         (write_object i vi s))"
  unfolding heap_ext_eq_def
proof
  fix k

  show
    "load_object k
       (write_object i vi
         (write_object j vj s))
     =
     load_object k
       (write_object j vj
         (write_object i vi s))"
    using IJ
    by (rule write_object_commute_load)
qed


(* ==========================================================================
   DOM writes inherit heap locality
   ========================================================================== *)

lemma load_object_write_dom_same:
  "load_object i
     (write_dom_element i tag props s)
   =
   Some (VDOMElement tag props)"
  unfolding write_dom_element.simps
  by (rule load_object_write_same)


lemma load_object_write_dom_independent:
  assumes IJ: "i ~= j"
  shows
    "load_object i
       (write_dom_element j tag props s)
     =
     load_object i s"
  unfolding write_dom_element.simps
  using IJ
  by (rule load_object_write_independent)


theorem write_dom_element_commute_ext:
  assumes IJ: "i ~= j"
  shows
    "heap_ext_eq
       (write_dom_element i tag props
         (write_dom_element j tag' props' s))
       (write_dom_element j tag' props'
         (write_dom_element i tag props s))"
  unfolding write_dom_element.simps
  using IJ
  by (rule write_object_commute_ext)


(* ==========================================================================
   change_element_color locality
   ========================================================================== *)

lemma load_object_change_color_independent:
  assumes IJ: "i ~= j"
  shows
    "load_object i
       (change_element_color j color s)
     =
     load_object i s"
proof (cases "load_object j s")

  case None

  then have C:
    "change_element_color j color s = s"
    by (simp add: change_element_color.simps)

  then show ?thesis
    by simp

next

  case (Some val)

  show ?thesis
  proof (cases val)

    case (VNumber x)

    have C:
      "change_element_color j color s = s"
      using Some VNumber
      by (simp add: change_element_color.simps)

    show ?thesis
      using C
      by simp

  next

    case VNaN

    have C:
      "change_element_color j color s = s"
      using Some VNaN
      by (simp add: change_element_color.simps)

    show ?thesis
      using C
      by simp

  next

    case (VBool x)

    have C:
      "change_element_color j color s = s"
      using Some VBool
      by (simp add: change_element_color.simps)

    show ?thesis
      using C
      by simp

  next

    case (VString x)

    have C:
      "change_element_color j color s = s"
      using Some VString
      by (simp add: change_element_color.simps)

    show ?thesis
      using C
      by simp

  next

    case VNull

    have C:
      "change_element_color j color s = s"
      using Some VNull
      by (simp add: change_element_color.simps)

    show ?thesis
      using C
      by simp

  next

    case VUndefined

    have C:
      "change_element_color j color s = s"
      using Some VUndefined
      by (simp add: change_element_color.simps)

    show ?thesis
      using C
      by simp

  next

    case (VRef x)

    have C:
      "change_element_color j color s = s"
      using Some VRef
      by (simp add: change_element_color.simps)

    show ?thesis
      using C
      by simp

  next

    case (VObject props)

    have C:
      "change_element_color j color s = s"
      using Some VObject
      by (simp add: change_element_color.simps)

    show ?thesis
      using C
      by simp

  next

    case (VWindow props)

    have C:
      "change_element_color j color s = s"
      using Some VWindow
      by (simp add: change_element_color.simps)

    show ?thesis
      using C
      by simp

  next

    case (VDOMElement tag props)

    have C:
      "change_element_color j color s =
       write_dom_element
         j
         tag
         (update_prop ''color'' (VString color) props)
         s"
      using Some VDOMElement
      by (simp add: change_element_color.simps)

    have W:
      "load_object i
         (write_dom_element
           j
           tag
           (update_prop ''color'' (VString color) props)
           s)
       =
       load_object i s"
      using IJ
      by (rule load_object_write_dom_independent)

    show ?thesis
      using C W
      by simp

  next

    case (VFunction params body env)

    have C:
      "change_element_color j color s = s"
      using Some VFunction
      by (simp add: change_element_color.simps)

    show ?thesis
      using C
      by simp

  next

    case (VBuiltin b)

    have C:
      "change_element_color j color s = s"
      using Some VBuiltin
      by (simp add: change_element_color.simps)

    show ?thesis
      using C
      by simp

  next

    case (VTypeError msg)

    have C:
      "change_element_color j color s = s"
      using Some VTypeError
      by (simp add: change_element_color.simps)

    show ?thesis
      using C
      by simp

  qed

qed


(* ==========================================================================
   Aliases used by higher-level proofs
   ========================================================================== *)

lemma write_object_observational_independent:
  assumes IJ: "i ~= j"
  shows
    "load_object i
       (write_object j v s)
     =
     load_object i s"
  using IJ
  by (rule load_object_write_independent)


lemma write_dom_element_observational_independent:
  assumes IJ: "i ~= j"
  shows
    "load_object i
       (write_dom_element j tag props s)
     =
     load_object i s"
  using IJ
  by (rule load_object_write_dom_independent)


lemma change_element_color_observational_independent:
  assumes IJ: "i ~= j"
  shows
    "load_object i
       (change_element_color j color s)
     =
     load_object i s"
  using IJ
  by (rule load_object_change_color_independent)

end