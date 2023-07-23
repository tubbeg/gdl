(def libgdx-version "1.12.0")

(defproject gdl "1.0-SNAPSHOT"
  :repositories [["jitpack" "https://jitpack.io"]] ; shapedrawer / grid2d
  :dependencies [[org.clojure/clojure "1.11.1"]

                 ; only @ dev profile ?
                 [nrepl "0.9.0"]
                 [org.clojure/tools.namespace "1.3.0"]

                 [com.badlogicgames.gdx/gdx                   ~libgdx-version]
                 [com.badlogicgames.gdx/gdx-platform          ~libgdx-version :classifier "natives-desktop"]
                 [com.badlogicgames.gdx/gdx-backend-lwjgl3    ~libgdx-version]
                 [com.badlogicgames.gdx/gdx-freetype          ~libgdx-version]
                 [com.badlogicgames.gdx/gdx-freetype-platform ~libgdx-version :classifier "natives-desktop"]

                 [space.earlygrey/shapedrawer "2.5.0"]]

  :javac-options ["-target" "1.8" "-source" "1.8" "-Xlint:-options"] ; TODO why ? libgdx ?

  :java-source-paths ["src-java"]

  :jvm-opts ["-XstartOnFirstThread"] ; for mac (TODO how to set without project.clj but just for my lein run ?)

  :profiles {:dev {:resource-paths ["test/resources"]}}

  :plugins [[lein-codox "0.10.8"]] ; TODO dev only ...

  :codox {:source-uri "https://github.com/damn/gdl/blob/main/{filepath}#L{line}"}

  :global-vars {*warn-on-reflection* true})

;; TODO dev
; - clojure.pprint => https://github.com/AbhinavOmprakash/snitch
; - intern them through user.clj somehow into clojure.core
; -XstartOnFirstThread
; - set repl ...
