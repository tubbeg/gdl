(ns gdl.context.image-drawer
  (:require gdl.protocols)
  (:import com.badlogic.gdx.graphics.Color
           com.badlogic.gdx.graphics.g2d.Batch))

(defn- draw-texture [^Batch batch texture [x y] [w h] rotation color]
  (if color (.setColor batch color))
  (.draw batch texture
         x
         y
         (/ w 2) ; rotation origin
         (/ h 2)
         w ; width height
         h
         1 ; scaling factor
         1
         rotation)
  (if color (.setColor batch Color/WHITE)))

(defn- unit-dimensions [unit-scale image]
  (if (= unit-scale 1)
    (:pixel-dimensions image)
    (:world-unit-dimensions image)))

(extend-type gdl.protocols.Context
  gdl.protocols/ImageDrawer
  (draw-image [this image x y]
    (gdl.protocols/draw-image this image [x y]))
  (draw-image [{:keys [batch unit-scale]}
               {:keys [texture color] :as image}
               position]
    (draw-texture batch texture position (unit-dimensions unit-scale image) 0 color))


  (draw-rotated-centered-image [{:keys [batch unit-scale]} {:keys [texture color] :as image} rotation [x y]]
    (let [[w h] (unit-dimensions unit-scale image)]
      (draw-texture batch
                    texture
                    [(- x (/ w 2))
                     (- y (/ h 2))]
                    [w h]
                    rotation
                    color)))

  (draw-centered-image [this image position]
    (gdl.protocols/draw-rotated-centered-image this image 0 position)))
