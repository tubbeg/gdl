(ns gdl.graphics.image
  (:require [gdl.assets :as assets]
            [gdl.graphics.world :as world])
  (:import com.badlogic.gdx.graphics.Color
           (com.badlogic.gdx.graphics.g2d Batch TextureRegion)))

; Explanation why not using libgdx Sprite class:
; * mutable fields
; * render in certain position/scale -> the sprite is modified somewhere else !
; * would have to reset it after every render ... or copy ?...
; * -> I cache only dimensions & scale for my texture-regions
; * color & rotation applied on rendering

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

(defn- unit-dimensions [{:keys [unit-scale] :as context} image]
  {:pre [(number? unit-scale)]}
  (cond
   (= unit-scale (:world/unit-scale context))
   (:world-unit-dimensions image)
   (= unit-scale (:gui/unit-scale context))
   (:pixel-dimensions image)))

(defn draw
  ([{:keys [batch] :as context} {:keys [texture color] :as image} position]
   (draw-texture batch texture position (unit-dimensions context image) 0 color))
  ([context image x y]
   (draw context image [x y])))

(defn draw-rotated-centered
  [{:keys [batch] :as context} {:keys [texture color] :as image} rotation [x y]]
  (let [[w h] (unit-dimensions context image)]
    (draw-texture batch
                  texture
                  [(- x (/ w 2))
                   (- y (/ h 2))]
                  [w h]
                  rotation
                  color)))

(defn draw-centered [context image position]
  (draw-rotated-centered context image 0 position))

(defn- texture-dimensions [^TextureRegion texture]
  [(.getRegionWidth  texture)
   (.getRegionHeight texture)])

(def pixel-dimensions :pixel-dimensions)
(def world-unit-dimensions :world-unit-dimensions)

(defn- assoc-dimensions [{:keys [texture scale] :as image}]
  {:pre [(or (number? scale)
             (and (vector? scale)
                  (number? (scale 0))
                  (number? (scale 1))))]}
  ; TODO here implicit assumption gui-unit-scale = 1 ...
  ; nope ! pixel-unit-scale is 1 !!!
  (let [pixel-dimensions (if (number? scale)
                           (mapv (partial * scale) (texture-dimensions texture))
                           scale)]
    (assoc image
           :pixel-dimensions pixel-dimensions
           :world-unit-dimensions (mapv (partial * world/unit-scale) pixel-dimensions))))

; (.getTextureData (.getTexture (:texture (first (:frames (:animation @(game.db/get-entity 1)))))))
; can remove :file @ Image because its in texture-data
; only TextureRegion doesn't have toString , can implement myself ? so can see which image is being used (in case)
(defrecord Image [file ; -> is in texture data, can remove.
                  texture ; -region ?
                  sub-image-bounds ; => is in texture-region data?
                  scale
                  pixel-dimensions
                  world-unit-dimensions
                  tilew
                  tileh])

(defn- get-texture-region [file & [x y w h]]
  (let [texture (assets/get-texture file)]
    (if (and x y w h)
      (TextureRegion. texture (int x) (int y) (int w) (int h))
      (TextureRegion. texture))))

(defn create
  "Scale can be a number or [width height]"
  [file & {:keys [scale]}]
  (assoc-dimensions
   (map->Image {:file file
                :scale (or scale 1)
                :texture (get-texture-region file)})))

(defn get-scaled-copy
  "Scaled of original texture-dimensions, not any existing scale."
  [image scale]
  (assoc-dimensions
   (assoc image :scale scale)))

(defn get-sub-image
  "Coordinates are from original image, not scaled one."
  [{:keys [file] :as image} & sub-image-bounds]
  (assoc-dimensions
   (assoc image
          :scale 1
          :texture (apply get-texture-region file sub-image-bounds)
          :sub-image-bounds sub-image-bounds)))

(defn spritesheet [file tilew tileh]
  (assoc (create file) :tilew tilew :tileh tileh))

(defn get-sprite [{:keys [tilew tileh] :as sheet} [x y]]
  (get-sub-image sheet (* x tilew) (* y tileh) tilew tileh))

(defn get-sheet-frames [sheet]
  (let [[w h] (:pixel-dimensions sheet)]
    (for [y (range (/ w (:tilew sheet)))
          x (range (/ h (:tileh sheet)))]
      (get-sprite sheet [x y]))))

(defn spritesheet-frames [& args]
  (get-sheet-frames (apply spritesheet args)))
