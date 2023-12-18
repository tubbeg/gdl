(ns gdl.simple-test
  (:require [gdl.app :as app]
            [gdl.protocols :refer [draw-circle draw-text generate-ttf]]
            gdl.screen)
  (:import com.badlogic.gdx.graphics.Color))

(defn draw-test [{:keys [special-font
                         gui-mouse-position
                         world-mouse-position] :as context}]
  (let [[wx wy] (map #(format "%.2f" %) world-mouse-position)
        [gx gy] gui-mouse-position
        the-str (str "World x " wx "\n"
                     "World y " wy "\n"
                     "GUI x " gx "\n"
                     "GUI y " gy "\n")]
    (draw-circle context gui-mouse-position 200 Color/WHITE)
    (draw-text context
               {:text (str "default-font\n" the-str)
                :x gx,:y gy,:h-align nil,:up? true})
    (draw-text context
               {:font special-font
                :text (str "exl-font\n" the-str)
                :x gx,:y gy,:h-align :left,:up? false})))

(defn create-context [context]
  {:special-font (generate-ttf context {:file "exocet/films.EXL_____.ttf"
                                        :size 16})
   :my-screen (reify gdl.screen/Screen
                (show [_ _context])
                (hide [_ _context])
                (render [_ context]
                  (app/render-view context :gui draw-test))
                (tick [_ _context _delta]))})

(defn app []
  (app/start {:app {:title "gdl demo"
                    :width 800
                    :height 600
                    :full-screen? false}
              :modules create-context
              :first-screen :my-screen}))
