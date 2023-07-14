(ns wrapper.space.earlygrey.shapedrawer.shapedrawer
  (:require [tortilla.wrap :as w]))

(defmethod tortilla.coerce/coerce-long Float [val _typ]
  (float val))

(defmulti coerce-ratio (fn [_val typ] typ))

(defmethod coerce-ratio Float [val _typ]
  (float val))

(extend-protocol tortilla.coerce/Coercible
  clojure.lang.Ratio
  (coerce [val typ]
    (coerce-ratio val typ)))

(w/defwrapper space.earlygrey.shapedrawer.ShapeDrawer)
