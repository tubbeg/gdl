(ns gdx.tiled
  (:require [data.grid2d :as grid])
  (:import [com.badlogic.gdx.maps MapLayer MapLayers MapProperties]
           [com.badlogic.gdx.maps.tiled TmxMapLoader TiledMap TiledMapTile TiledMapTileSet
            TiledMapTileLayer TiledMapTileLayer$Cell]))

(defn load-map
  "Requires OpenGL context (texture generation)."
  [file]
  (.load (TmxMapLoader.) file))

(defn dispose [^TiledMap tiled-map]
  (.dispose tiled-map))

; TODO this is actually get-properties for no reflection
(defmulti get-property (fn [obj k] (class obj)))

(defmethod get-property TiledMap [^TiledMap tiled-map k]
  (.get (.getProperties tiled-map) (name k)))

(defmethod get-property TiledMapTile [^TiledMapTile tile k]
  (.get (.getProperties tile) (name k)))

(defmethod get-property TiledMapTileLayer [^MapLayer layer k]
  (.get (.getProperties layer) (name k)))

; TODO before var name or arglist put type hint?
; https://clojure.org/reference/java_interop#typehints
; "For function return values, the type hint can be placed before the arguments vector:"
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
; => extend multi getProperties with this.. above. TODO
; TODO slow => use directly get-property
#_(defn properties [obj]
    (let [^MapProperties ps (.getProperties obj)]
      (zipmap (map keyword (.getKeys ps)) (.getValues ps))))
