theory JSFrameRule
imports JSObsEquiv JSFuel
begin

(* ==========================================================================
   Frame Rules and Event Sequences

   IMPORTANT:
   We do not assume that an event handler is unaffected merely because a
   different heap cell was changed.  make_event_handler eventually executes
   run_handler on the complete state, so such an equality would be too strong.

   Instead:
   1. locality of DOM writes is stated through heap_ext_eq;
   2. event-level reordering uses explicit assumptions about the two
      intermediate executions;
   3. observational equivalence is inherited once the intermediate results
      are known to be observationally equivalent.
   ========================================================================== *)


(* ==========================================================================
   Heap-level frame rule
   ========================================================================== *)

theorem frame_rule_write_object:
  assumes IJ: "i ~= j"
  shows
    "heap_ext_eq
       (write_object i vi
         (write_object j vj s))
       (write_object j vj
         (write_object i vi s))"
  using IJ
  by (rule write_object_commute_ext)


theorem frame_rule_write_dom_element:
  assumes IJ: "i ~= j"
  shows
    "heap_ext_eq
       (write_dom_element i tag_i props_i
         (write_dom_element j tag_j props_j s))
       (write_dom_element j tag_j props_j
         (write_dom_element i tag_i props_i s))"
  using IJ
  by (rule write_dom_element_commute_ext)


(* ==========================================================================
   Locality of color change

   Changing j cannot change the value observed by loading a distinct i.
   This is the key footprint property available in JSLocality.
   ========================================================================== *)

lemma frame_rule_change_color_load:
  assumes IJ: "i ~= j"
  shows
    "load_object i
       (change_element_color j color s)
     =
     load_object i s"
  using IJ
  by (rule load_object_change_color_independent)


(* ==========================================================================
   Event sequences
   ========================================================================== *)

fun run_events ::
  "(js_event_kind * nat) list => js_state => js_state"
where
  "run_events [] s = s"
| "run_events ((ev, target) # rest) s =
     run_events rest
       (make_event_handler ev target s)"


lemma run_events_Nil:
  "run_events [] s = s"
  by simp


lemma run_events_single:
  "run_events [(ev, i)] s =
   make_event_handler ev i s"
  by simp


lemma run_events_two:
  "run_events [(ev_i, i), (ev_j, j)] s =
   make_event_handler ev_j j
     (make_event_handler ev_i i s)"
  by simp


(* ==========================================================================
   Sound event-level frame rule

   Unlike the previous version, the assumptions describe the ACTUAL
   intermediate states on which the second handler executes.

   The old formulation only described each handler on the initial state s,
   which was insufficient to justify its behavior after another handler had
   already modified the state.
   ========================================================================== *)

theorem frame_rule_events:
  assumes LEFT:
    "make_event_handler ev_j j
       (make_event_handler ev_i i s) =
     left_state"
  and RIGHT:
    "make_event_handler ev_i i
       (make_event_handler ev_j j s) =
     right_state"
  and OBS:
    "obs_equiv left_state right_state p"
  shows
    "obs_equiv
       (make_event_handler ev_j j
         (make_event_handler ev_i i s))
       (make_event_handler ev_i i
         (make_event_handler ev_j j s))
       p"
  using LEFT RIGHT OBS
  by simp


(* ==========================================================================
   Frame rule specialized to handlers whose behavior is known on the
   intermediate states.

   This is the useful form for proving concrete independent handlers.
   ========================================================================== *)

theorem frame_rule_events_by_effect:
  assumes HI:
    "make_event_handler ev_i i
       (make_event_handler ev_j j s) =
     change_element_color i ci
       (make_event_handler ev_j j s)"
  and HJ:
    "make_event_handler ev_j j
       (make_event_handler ev_i i s) =
     change_element_color j cj
       (make_event_handler ev_i i s)"
  and OBS:
    "obs_equiv
       (change_element_color j cj
         (make_event_handler ev_i i s))
       (change_element_color i ci
         (make_event_handler ev_j j s))
       p"
  shows
    "obs_equiv
       (make_event_handler ev_j j
         (make_event_handler ev_i i s))
       (make_event_handler ev_i i
         (make_event_handler ev_j j s))
       p"
  using HI HJ OBS
  by simp


(* ==========================================================================
   Reordering of two events

   The theorem is now phrased directly over run_events.  The required
   observational condition concerns the actual two execution orders, so
   there is no unsound inference from facts that hold only in the initial
   state.
   ========================================================================== *)

theorem events_reorder_two:
  assumes FRAME:
    "obs_equiv
       (make_event_handler ev_j j
         (make_event_handler ev_i i s))
       (make_event_handler ev_i i
         (make_event_handler ev_j j s))
       p"
  shows
    "obs_equiv
       (run_events [(ev_i, i), (ev_j, j)] s)
       (run_events [(ev_j, j), (ev_i, i)] s)
       p"
  using FRAME
  by simp


(* ==========================================================================
   A stronger reusable version with intermediate-state assumptions
   ========================================================================== *)

theorem events_reorder_two_by_effect:
  assumes HI:
    "make_event_handler ev_i i
       (make_event_handler ev_j j s) =
     si"
  and HJ:
    "make_event_handler ev_j j
       (make_event_handler ev_i i s) =
     sj"
  and OBS:
    "obs_equiv sj si p"
  shows
    "obs_equiv
       (run_events [(ev_i, i), (ev_j, j)] s)
       (run_events [(ev_j, j), (ev_i, i)] s)
       p"
proof -
  have L:
    "run_events [(ev_i, i), (ev_j, j)] s = sj"
    using HJ
    by simp

  have R:
    "run_events [(ev_j, j), (ev_i, i)] s = si"
    using HI
    by simp

  show ?thesis
    using L R OBS
    by simp
qed


(* ==========================================================================
   Absorption law for repeated writes to the SAME element

   The last color wins.
   ========================================================================== *)

lemma change_element_color_absorbs:
  "change_element_color i c2
     (change_element_color i c1 s)
   =
   change_element_color i c2 s"
proof (cases "load_object i s")

  case None

  then show ?thesis
    by (simp add: change_element_color.simps)

next

  case (Some v)

  show ?thesis
  proof (cases v)

    case (VNumber x)

    then show ?thesis
      using Some
      by (simp add: change_element_color.simps)

  next

    case VNaN

    then show ?thesis
      using Some
      by (simp add: change_element_color.simps)

  next

    case (VBool x)

    then show ?thesis
      using Some
      by (simp add: change_element_color.simps)

  next

    case (VString x)

    then show ?thesis
      using Some
      by (simp add: change_element_color.simps)

  next

    case VNull

    then show ?thesis
      using Some
      by (simp add: change_element_color.simps)

  next

    case VUndefined

    then show ?thesis
      using Some
      by (simp add: change_element_color.simps)

  next

    case (VRef x)

    then show ?thesis
      using Some
      by (simp add: change_element_color.simps)

  next

    case (VObject ps)

    then show ?thesis
      using Some
      by (simp add: change_element_color.simps)

  next

    case (VWindow ps)

    then show ?thesis
      using Some
      by (simp add: change_element_color.simps)

  next

    case (VDOMElement tag props)

    define props1 where
      "props1 =
       update_prop ''color'' (VString c1) props"

    define props2 where
      "props2 =
       update_prop ''color'' (VString c2) props"

    have STEP1:
      "change_element_color i c1 s =
       write_dom_element i tag props1 s"
      using Some VDOMElement
      unfolding props1_def
      by simp

    have LOAD1:
      "load_object i
         (write_dom_element i tag props1 s) =
       Some (VDOMElement tag props1)"
      by (rule load_object_write_dom_same)

    have STEP2:
      "change_element_color i c2
         (write_dom_element i tag props1 s) =
       write_dom_element i tag
         (update_prop ''color'' (VString c2) props1)
         (write_dom_element i tag props1 s)"
      using LOAD1
      by simp

    have PROP:
      "update_prop ''color'' (VString c2) props1 =
       props2"
      unfolding props1_def props2_def
    proof (induct props)
      case Nil
      then show ?case
        by simp
    next
      case (Cons a props)
      then show ?case
        by (cases a)
           (auto split: if_split)
    qed

    have WRITE:
      "write_dom_element i tag props2
         (write_dom_element i tag props1 s)
       =
       write_dom_element i tag props2 s"
      unfolding write_dom_element.simps
      by (simp add: write_object.simps)

    have DIRECT:
      "change_element_color i c2 s =
       write_dom_element i tag props2 s"
      using Some VDOMElement
      unfolding props2_def
      by simp

    show ?thesis
      unfolding STEP1 STEP2 PROP
      using WRITE DIRECT
      by simp

  next

    case (VFunction params body env)

    then show ?thesis
      using Some
      by (simp add: change_element_color.simps)

  next

    case (VBuiltin b)

    then show ?thesis
      using Some
      by (simp add: change_element_color.simps)

  next

    case (VTypeError msg)

    then show ?thesis
      using Some
      by (simp add: change_element_color.simps)

  qed

qed


theorem write_absorption_law:
  "obs_equiv
     (change_element_color i c2
       (change_element_color i c1 s))
     (change_element_color i c2 s)
     p"
proof -
  have EQ:
    "change_element_color i c2
       (change_element_color i c1 s)
     =
     change_element_color i c2 s"
    by (rule change_element_color_absorbs)

  show ?thesis
    using EQ
    by (rule state_eq_imp_obs_equiv)
qed


(* ==========================================================================
   Concrete executable checks
   ========================================================================== *)

value
  "change_element_color 1 ''blue''
     (change_element_color 2 ''red'' dom_state)"

value
  "change_element_color 2 ''red''
     (change_element_color 1 ''blue'' dom_state)"

value
  "run_events
     [(EvClick, 1), (EvMouseOver, 2)]
     dom_state"

end