(defproject gdx "1.0-SNAPSHOT"
  :repositories [["jitpack" "https://jitpack.io"]] ; shapedrawer / grid2d
  :dependencies [[org.clojure/clojure "1.11.1"]
                 [nrepl "0.9.0"]
                 [org.clojure/tools.namespace "1.3.0"]
                 [com.badlogicgames.gdx/gdx                "1.11.0"]
                 [com.badlogicgames.gdx/gdx-backend-lwjgl3 "1.11.0"]
                 [com.badlogicgames.gdx/gdx-platform       "1.11.0" :classifier "natives-desktop"]
                 [space.earlygrey/shapedrawer "2.5.0"]]
  :javac-options ["-target" "1.8" "-source" "1.8" "-Xlint:-options"]
  :java-source-paths ["src-java"]
  ;:jvm-opts ["-XstartOnFirstThread"] ; for mac
  :profiles {:dev {:resource-paths ["test/resources"]}}
  :plugins [[lein-codox "0.10.8"]]
  :codox {:source-uri "https://github.com/damn/gdx/blob/main/{filepath}#L{line}"}
  :global-vars {*warn-on-reflection* true})
