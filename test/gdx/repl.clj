(ns gdx.repl
  (:require [gdx.dev-loop :refer [dev-loop]]
            [nrepl.server :refer [start-server]]
            [clojure.tools.namespace.repl :refer [disable-reload!]]))

(disable-reload!)

(defn -main []
  (defonce nrepl-server (start-server :port 7888))
  (println "Started nrepl server on port 7888.")
  (dev-loop))
