(ns gdl.scene2d.actor
  (:refer-clojure :exclude [name]))

(defprotocol Actor
  (id [_])
  (set-id! [_ id])
  (set-name! [_ name])
  (name [_])
  (visible? [_])
  (set-visible! [_ bool])
  (toggle-visible! [_])
  (set-position! [_ x y])
  (set-center! [_ x y])
  (set-width! [_ width])
  (set-height! [_ height])
  (get-x [_])
  (get-y [_])
  (width [_])
  (height [_])
  (set-touchable! [_ touchable] ":children-only, :disabled or :enabled.")
  (add-listener! [_ listener] "Add a listener to receive events that hit this actor.")
  (add-tooltip! [_ tooltip-text] "tooltip-text is a (fn [context] )")
  (remove-tooltip! [_])
  (remove! [_] "Removes this actor from its parent, if it has a parent.")
  (parent [_] "Returns the parent actor, or null if not in a group.")
  (find-ancestor-window [_])
  (pack-ancestor-window! [_]))
