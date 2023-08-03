(ns gdl.app
  (:require [gdl.utils :refer :all])
  (:import [com.badlogic.gdx Gdx Application]))

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

(declare ^:priate ^Application app)

(defn load-state [log-level]
  (set-var-root #'app Gdx/app)
  (.setLogLevel app Application/LOG_DEBUG))

(defn application-listener []
  (.getApplicationListener app))

(defn exit []
  (.exit app))

(defn log-debug [tag message]
  (.debug app tag message))

; TODO naming ...
(defmacro with-context [& exprs]
  `(.postRunnable app (fn [] ~@exprs)))
