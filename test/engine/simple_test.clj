(ns engine.simple-test
  (:require [engine.tiled :as tiled]
            [engine.graphics :refer :all]
            [engine.input :refer :all]
            [engine.core :refer :all]))

(import '[com.badlogic.gdx Gdx])
(import 'com.badlogic.gdx.graphics.g2d.freetype.FreeTypeFontGenerator)
(import 'com.badlogic.gdx.graphics.g2d.freetype.FreeTypeFontGenerator$FreeTypeFontParameter)

(defn- load-resources []
 (def sheet (spritesheet "items.png" 16 16))
 (def sprite (get-sprite sheet [5 4]))

 (let [generator (FreeTypeFontGenerator. (.internal (Gdx/files) "exocet/films.EXH_____.ttf"))
       parameter (FreeTypeFontGenerator$FreeTypeFontParameter.)]
   (set! (.size parameter) 32)
   ;(set! (.borderWidth parameter) 1)
   ;(set! (.borderColor parameter) red)
   (def font12 (.generateFont generator parameter))
   (set! (.markupEnabled (.getData font12)) true)
   (.dispose generator)
   ))



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
  #_(render-readable-text 0 0 {} ^{:scale 0.5} [(str (get-fps) " FPS")])

  #_(.draw font12
         (deref #'engine.graphics/*batch*)
         "foo bar BAZ !!! zzz"
         (float 20)
         (float 20))

  #_(.draw font12
         (deref #'engine.graphics/*batch*)
         "[GRAY]Sword,[] Action-time: 0.5s, [RED]Damage: 5-10"
         (float 500)
         (float 300))

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
                           (str "Screen Y" sy)]
                          )
    #_(.draw font12
           (deref #'engine.graphics/*batch*)
           (apply str
                  [(str "Map x " x)
                   (str "Map y " y)
                   (str "GUI x " gx)
                   (str "GUI y " gy)
                   (str "Screen X" sx)
                   (str "Screen Y" sy)])
           (float 100)
           (float 60))
    )

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
      (ui/create-ui)
     ; (def tiled-map (tiled/load-map "example.tmx"))  ; TODO init ...
      ;(set-camera-position! [0 0])

      )
    (destroy [_]
      #_(tiled/dispose tiled-map)

      )
    (render [_]
      ;(render-map tiled-map
      ;            (fn [color x y] white))
      ;(render-map-level map-content)
      (render-gui-level gui-render)
      )
    (update-screen [_ delta])))

(defn app []
  (start-app :full-screen false
             :title "engine demo"
             :window-width 1400
             :window-height 800
             :viewport-width 1400
             :viewport-height 800
             :assets-folder "test/resources/"
             :game-screens {:main game-screen}
             :on-create load-resources
             :tile-size 16))
