
; TODO link libgdx docs (wiki/javadoc) at every
; ns / etc. ?



; For function return values, the type hint can be placed before the arguments vector:
; (defn hinted-single ^String [])
; I put before var ?

(defproject gdx "1.0-SNAPSHOT"
  :repositories [["jitpack" "https://jitpack.io"]] ; shapedrawer / grid2d
  :dependencies [[org.clojure/clojure "1.11.1"]

                 ; TODO only dev?
                 [nrepl "0.9.0"]
                 [org.clojure/tools.namespace "1.3.0"]

                 ; TODO update libgdx
                 [com.badlogicgames.gdx/gdx                       "1.11.0"]
                 [com.badlogicgames.gdx/gdx-backend-lwjgl3        "1.11.0"]
                 [com.badlogicgames.gdx/gdx-platform              "1.11.0" :classifier "natives-desktop"]
                 [com.badlogicgames.gdx/gdx-freetype-platform     "1.11.0" :classifier "natives-desktop"]
                 [com.badlogicgames.gdx/gdx-freetype              "1.10.0"]

                 [space.earlygrey/shapedrawer "2.5.0"]

                 [com.github.damn/grid2d "1.0"]

                 ]

  :javac-options ["-target" "1.8" "-source" "1.8" "-Xlint:-options"] ; ??? TODO

  :java-source-paths ["src-java"]

  :jvm-opts ["-XstartOnFirstThread"] ; for mac

  ; TODO set resources/ here also and otherwise test/resources
  :profiles {:dev {:resource-paths ["test/resources"]}}

  :plugins [[lein-codox "0.10.8"]]

  :codox {:namespaces [gdx.core
                       gdx.graphics
                       gdx.input
                       gdx.tiled]}

  :global-vars {*warn-on-reflection* true}
  )

; TODO:

; * run warn on reflection test on all new code

; * make jar file of game (see with assets cannot list in jar with libgdx)
; -> create edn file with resoures folder content and read it -> simple

; * font only 'simple_6x8.png' at the moment

; shifting the window with the bar breaks the fitviewport (fixed with g/on-resize ?)

; TODO

; license?

; https://www.reddit.com/r/Clojure/comments/yqj4m9/minimal_clojure_2d_game_engine_for_desktop_based/
; https://news.ycombinator.com/item?id=33531048
; https://clojurians.slack.com/archives/C066UV2MV/p1668000422880709

; TODO BUG
;[com.badlogicgames.gdx/gdx-lwjgl3-glfw-awt-macos "1.11.0"] ; TODO not working
; isKeyJustPressed & isButtonJustPressed does not trigger consistently at '1.11.0' with gdx-lwjgl3-glfw-awt-macos
; is fixed when using -XstartOnFirstThread and not glfw-awt-macos
; export LEIN_JVM_OPTS='-XstartOnFirstThread'
