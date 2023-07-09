(ns engine.tiled
  (:require [data.grid2d :as grid])
  (:import [com.badlogic.gdx.maps MapLayer MapLayers MapProperties]
           [com.badlogic.gdx.maps.tiled TmxMapLoader TiledMap TiledMapTile
            TiledMapTileLayer TiledMapTileLayer$Cell]))

(defn load-map
  "Requires OpenGL context (texture generation)."
  [file]
  (.load (TmxMapLoader.) file))

(defn dispose [tiled-map]
  (.dispose tiled-map))

; TODO this is actually get-properties for no reflection
(defmulti get-property (fn [obj k] (class obj)))

(defmethod get-property TiledMap [^TiledMap tiled-map k]
  (.get (.getProperties tiled-map) (name k)))

(defmethod get-property TiledMapTile [^TiledMapTile tile k]
  (.get (.getProperties tile) (name k)))

(defmethod get-property TiledMapTileLayer [^MapLayer layer k]
  (.get (.getProperties layer) (name k)))

(defn ^MapLayers layers [tiled-map]
  (.getLayers ^TiledMap tiled-map))

(defn layer-name [layer]
  (if (keyword? layer)
    (name layer)
    (.getName ^MapLayer layer)))

(defn layer-index [tiled-map layer]
  (let [idx (.getIndex (layers tiled-map) ^String (layer-name layer))]
    (when-not (= -1 idx)
      idx)))

(defn- get-layer [tiled-map layer-name]
  (.get (layers tiled-map) ^String layer-name))

(defn remove-layer! [tiled-map layer]
  (.remove (layers tiled-map)
           ^Integer (layer-index tiled-map layer)))

(defn ^TiledMapTileLayer$Cell cell-at [[x y] tiled-map layer]
  (when-let [layer (get-layer tiled-map (layer-name layer))]
    (.getCell ^TiledMapTileLayer layer x y)))

(defn property-value
  "Returns the property value from layer and position.
  If there is no cell returns :no-cell and if the property value is undefined returns :undefined."
  [position tiled-map layer property]
  {:pre [(keyword? property)]}
  (if-let [cell (cell-at position tiled-map layer)]
    (if-let [value (get-property (.getTile cell) property)]
      value
      :undefined)
    :no-cell))

(defn width [tiled-map]
  (get-property tiled-map :width))

(defn height [tiled-map]
  (get-property tiled-map :height))

(defn- map-positions [tiled-map]
  (for [x (range (width  tiled-map))
        y (range (height tiled-map))]
    [x y]))

(defn positions-with-property [tiled-map layer property]
  (when (layer-index tiled-map layer)
    (for [position (map-positions tiled-map)
          :let [[x y] position
                value (property-value position tiled-map layer property)]
          :when (not (#{:undefined :no-cell} value))]
      [position value])))

; reflection at .getProperties, but obj unknown (MapLayer or TileSet, ..)
; TODO slow => use directly get-property
(defn properties [obj]
  (let [^MapProperties ps (.getProperties obj)]
    (zipmap (map keyword (.getKeys ps)) (.getValues ps))))

(defn- tilesets [tiled-map]
  (map (fn [tileset]
         {:name (.getName tileset)
          :size (.size tileset)
          :properties (properties tileset)})
       (.getTileSets tiled-map)))

; TODO all unused down from here

; Useful for calculating new localids after increasing spritesheets width
; increase spritesheet width from 4 to 7 and update localids:
; (convert-to-localid (convert-to-spriteposi localid 4) 7)
#_(defn- convert-to-localid [[x y] sheetw]
    (+ x (* y sheetw)))

(defn convert-to-spriteposi [localid sheetw]
  {:post [(integer? (% 0))
          (integer? (% 1))]}
  (assert (and (integer? localid) (>= localid 0)) (str "localid: " localid))
  [(mod localid sheetw)
   (int (/ localid sheetw))])

(defn- firstgid [tileset]
  (:firstgid (:properties tileset)))

(defn- tile->tileset [tiled-map ^TiledMapTile tile]
  (let [gid (.getId tile)
        tilesets (tilesets tiled-map)]
    (apply max-key firstgid
           (filter #(>= gid (firstgid %)) tilesets))))

(defn- tileset-width [tileset]
  (/ (:imagewidth (:properties tileset))
     (:tilewidth  (:properties tileset))))

(defn get-spriteidx [position tiled-map layer] ; TODO unused
  (if-let [cell (cell-at position tiled-map layer)]
    (let [tile (.getTile cell)
          tileset (tile->tileset tiled-map tile)
          gid (.getId tile)]
      (convert-to-spriteposi (- gid (firstgid tileset))
                             (tileset-width tileset)))))
