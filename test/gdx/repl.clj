(ns gdx.repl
  (:require [gdx.dev-loop :refer [dev-loop]]
            [nrepl.server :refer [start-server]]
            [clojure.tools.namespace.repl :refer [disable-reload!]]))

(disable-reload!)

(defn -main []
  (let [port 7889]
    (defonce nrepl-server (start-server :port port))
    (println "Started nrepl server on port " port))
  (dev-loop))
