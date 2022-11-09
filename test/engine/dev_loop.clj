(ns engine.dev-loop
  (:require [clojure.tools.namespace.repl :refer [refresh-all]]
            [engine.simple-test :refer [app]]))

; refresh-all because global state in engine.core/initialize


(println "engine.dev-loop")

(defn dev-loop []
  (app)
  (refresh-all :after 'engine.dev-loop/dev-loop))
