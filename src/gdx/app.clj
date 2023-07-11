(ns gdx.app
  (:import [com.badlogic.gdx Application Gdx]))

(defn ^Application app []
  (Gdx/app))

(defn exit []
  (.exit app))

(defmacro post-runnable [& exprs]
  `(.postRunnable app (fn [] ~@exprs)))

(def ^:private on-create-fns  [])
(def ^:private on-destroy-fns [])

(defmacro on-create  [& exprs] `(alter-var-root #'on-create-fns  conj (fn [] ~@exprs)))
(defmacro on-destroy [& exprs] `(alter-var-root #'on-destroy-fns conj (fn [] ~@exprs)))

(defn ^:no-doc call-on-create-fns!  [] (doseq [f on-create-fns]  (f)))
(defn ^:no-doc call-on-destroy-fns! [] (doseq [f on-destroy-fns] (f)))
