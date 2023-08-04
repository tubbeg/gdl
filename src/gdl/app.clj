(ns gdl.app
  (:require [gdl.utils :refer :all])
  (:import com.badlogic.gdx.Application))

(declare ^Application app)

(defn application-listener []
  (.getApplicationListener app))

(defn exit []
  (.exit app))

(defn log-debug [tag message]
  (.debug app tag message))

; TODO naming ...
(defmacro with-context [& exprs]
  `(.postRunnable app (fn [] ~@exprs)))

;;

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
