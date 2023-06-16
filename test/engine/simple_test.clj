(ns engine.simple-test
  (:require [engine.tiled :as tiled]
            [engine.graphics :refer :all]
            [engine.input :refer :all]
            [engine.core :refer :all]))

(defn- load-resources []
 (def sheet (spritesheet "items.png" 16 16))
 (def sprite (get-sprite sheet [5 4])))

(defn map-content []
  ;(draw-grid 0 0 24 18 1 1 (darker white 0.5))
  ;(draw-line 10 10 12 12 red)
  ;(draw-centered-image test-image-1 [12 6])
  ;(fill-rect 12 6 1 1 white)


  ; draw text at [11 10]
  ;(render-readable-text 5 10 {:scale 0.5} "draw-string scale 0.5")
  ;(render-readable-text 5 12 {} "draw-string scale 1")
  ;(render-readable-text 5 14 {:scale 2.5} "scale 2.5")

  (let [[x y] (map-coords)
        w 4.5
        h 3.5
        ]
    (draw-rect x y w h white)
    (fill-ellipse
     [(+ x (/ w 2)) (+ y (/ h 2))]
     (* 1 (/ w 2))
     (* 1 (/ h 2))
     (rgbcolor 1 0 0 0.5))

     (draw-sector
      [x y]
      2
      0
      45
      red

      )



    #_(render-readable-text x y
                            {:centerx true :centery true :shift false :scale 1}
                            ["Colored Font test"
                             red
                             "red"
                             blue
                             "blue"
                             3
                             yellow
                             "yellow"]))

  )

(defn gui-render []
  (render-readable-text 0 0 {} ^{:scale 0.5} [(str (get-fps) " FPS")])

  (let [[x y] (map #(format "%.2f" %) (map-coords))
        [gx gy] (mouse-coords)
        [sx sy] (get-mouse-pos)]
    (render-readable-text 0 60
                          {:shift true}
                          [(str "Map x " x)
                           (str "Map y " y)
                           (str "GUI x " gx)
                           (str "GUI y " gy)
                           (str "Screen X" sx)
                           (str "Screen Y" sy)]))

  #_(let [[x y] (mouse-coords)]
    (render-readable-text x y
                          {:centerx true :centery true :shift true}
                          ^{:scale 1.5}
                          ["Colored Font test foo"
                           red
                           "red"
                           blue
                           "blue"
                           3
                           yellow
                           "yellow"])))

(def game-screen
  (reify GameScreen
    (show [_]
      (def tiled-map (tiled/load-map "example.tmx"))  ; TODO init ...
      (set-camera-position! [0 0]))
    (destroy [_]
      (tiled/dispose tiled-map))
    (render [_]
      (render-map tiled-map
                  (fn [color x y] white))
      (render-map-level map-content)
      (render-gui-level gui-render))
    (update-screen [_ delta])))

(defn app []
  (start-app :full-screen false
             :title "engine demo"
             :window-width 1400
             :window-height 800
             :viewport-width 600
             :viewport-height 400
             :assets-folder "test/resources/"
             :game-screens {:main game-screen}
             :on-create load-resources
             :tile-size 16))
