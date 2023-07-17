(ns gdx.simple-test
  (:require [gdx.app :as app]
            [gdx.game :as game]
            [gdx.graphics :as g]
            [gdx.input :as input]))

#_(defn tortilla-performance-test []
  (println)
  (let [n 100000
        args [[300 400] 50 100 g/white]]
    (println "tortilla")
    (time (dotimes [_ n] (apply g/filled-ellipse-tortilla args)))
    (println "type hint")
    (time (dotimes [_ n] (apply g/filled-ellipse-type-hint args)))
    (println "reflection")
    (time (dotimes [_ n] (apply g/filled-ellipse-reflection args)))

    )
  (println)

  ;tortilla
  ;"Elapsed time: 2443.44484 msecs"
  ;type hint
  ;"Elapsed time: 1280.779603 msecs"
  ;reflection
  ;"Elapsed time: 1724.707907 msecs"

  ; slower than reflection! whole tortilla library pointless.

  ; => try defwrapper from cljc.java-time
  ; https://github.com/henryw374/cljc.java-time/blob/master/dev/defwrapper.clj#L205
  )

; TODO use @ cdq/game/ui/debug-window
(defn render-mouse-coordinates []
  (let [[x y] (map #(format "%.2f" %) (g/map-coords))
        [gx gy] (g/mouse-coords)
        [sx sy] (input/get-mouse-pos) ; TODO same as mouse-coords ?
        the-str (str
                 "Map x " x "\n"
                 "Map y " y "\n"
                 "GUI x " gx "\n"
                 "GUI y " gy "\n"
                 "Screen X" sx "\n"
                 "Screen Y" sy)]
    (g/draw-text the-str 200 155)))

(defn render []
  (render-mouse-coordinates)
  #_(tortilla-performance-test))

(game/defscreen screen
  :show (fn [])
  :render (fn [] (g/render-gui render))
  :destroy (fn [])
  :update (fn [delta]))


(defn app []
  (app/create (game/create {:main screen})
              {:title "gdx demo"
               :width 800
               :height 600
               :full-screen false}))
