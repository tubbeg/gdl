(ns gdl.app
  (:require [gdl.utils :refer :all])
  (:import com.badlogic.gdx.Application))

(declare ^Application app)

(defn exit []
  (.exit app))

(defmacro with-context [& exprs]
  `(.postRunnable app (fn [] ~@exprs)))

;; TODO remove ! manage state centrally not automagically.

(defmacro on-create  [& exprs] `(on :app/create  ~@exprs))
(defmacro on-destroy [& exprs] `(on :app/destroy ~@exprs))

(defmacro defmanaged [symbol init]
  `(do
    (declare ~symbol)

    (let [var# (var ~symbol)]
      (on-create
       (set-var-root var# ~init))

      (on-destroy
       (when (:dispose (meta var#))
         (dispose ~symbol))))))
