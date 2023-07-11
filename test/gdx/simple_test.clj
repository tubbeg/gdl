(ns gdx.simple-test
  (:require [gdx.app :as app]
            [gdx.game :as game]
            [gdx.lwjgl :as lwjgl]
            [gdx.tiled :as tiled]
            [gdx.graphics :as g]
            [gdx.input :as input]
            [gdx.utils :refer (set-var-root)]))

(import '[com.badlogic.gdx Gdx])
(import 'com.badlogic.gdx.graphics.g2d.freetype.FreeTypeFontGenerator)
(import 'com.badlogic.gdx.graphics.g2d.freetype.FreeTypeFontGenerator$FreeTypeFontParameter)

(app/on-create
 ;(def sheet (g/spritesheet "items.png" 16 16))
 ;(def sprite (g/get-sprite sheet [5 4]))

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

  (let [[x y] (g/map-coords)
        w 4.5
        h 3.5
        ]
    (g/draw-rect x y w h g/white)
    (g/fill-ellipse
     [(+ x (/ w 2)) (+ y (/ h 2))]
     (* 1 (/ w 2))
     (* 1 (/ h 2))
     (g/rgbcolor 1 0 0 0.5))

     (g/draw-sector
      [x y]
      2
      0
      45
      g/red

      )



    #_(g/render-readable-text x y
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
  #_(g/render-readable-text 0 0 {} ^{:scale 0.5} [(str (get-fps) " FPS")])

  (.draw font12
         (deref #'gdx.graphics/*batch*)
         "foo bar BAZ !!! zzz"
         (float 20)
         (float 20))

  #_(.draw font12
         (deref #'gdx.graphics/*batch*)
         "[GRAY]Sword,[] Action-time: 0.5s, [RED]Damage: 5-10"
         (float 500)
         (float 300))

  (let [[x y] (map #(format "%.2f" %) (g/map-coords))
        [gx gy] (g/mouse-coords)
        [sx sy] (input/get-mouse-pos)]
    (g/render-readable-text 0 60
                          {:shift true}
                          [(str "Map x " x)
                           (str "Map y " y)
                           (str "GUI x " gx)
                           (str "GUI y " gy)
                           (str "Screen X" sx)
                           (str "Screen Y" sy)]
                          )
    #_(.draw font12
           (deref #'gdx.graphics/*batch*)
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

  #_(let [[x y] (g/mouse-coords)]
      (g/render-readable-text x y
                            {:centerx true :centery true :shift true}
                            ^{:scale 1.5}
                            ["Colored Font test foo"
                             g/red
                             "red"
                             g/blue
                             "blue"
                             3
                             g/yellow
                             "yellow"])))

(game/defscreen screen
  :show (fn [])
  :render (fn []
            ;(render-map tiled-map
            ;            (fn [color x y] white))
            ;(render-map-level map-content)
            (g/render-gui-level gui-render)
            )
  :destroy (fn []
             ;(tiled/dispose tiled-map)

             )
  :update (fn [delta]))

; TODO set world unit scale

(set-var-root #'g/world-unit-scale 1)

(defn start-app []
  (lwjgl/create-app :game (game/create {:main screen})
                    :title "gdx demo"
                    :width 800
                    :height 600
                    :full-screen false))
