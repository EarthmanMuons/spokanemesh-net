// SPDX-License-Identifier: 0BSD
// Copyright (c) 2025 Aaron Bull Schaefer and contributors

"use strict";

// --- CONSTANTS ---

const NodeType = { CLIENT: "client", REPEATER: "repeater" };

const NODE_DEFAULT = {
  [NodeType.CLIENT]: {
    count: 25,
    size: 15, // px circumradius of client hexagon
    hitbox: 12, // px radius for proximity detection
    range: 160, // px max transmission range
    rangeVariance: 60, // px +/- offset for range
    useGrid: false,
    color: getCssColor("--client-fill"),
    borderColor: getCssColor("--client-stroke"),
  },
  [NodeType.REPEATER]: {
    count: 10,
    size: 25, // px circumradius of repeater hexagon
    hitbox: 20, // px radius for proximity detection
    range: 280, // px max transmission range
    rangeVariance: 70, // px +/- offset for range
    useGrid: true,
    color: getCssColor("--repeater-fill"),
    borderColor: getCssColor("--repeater-stroke"),
  },
};

const RoutingStrategy = {
  DIRECT: "unicast",
  FLOOD: "broadcast",
};

const PACKET_DEFAULT = {
  [RoutingStrategy.DIRECT]: {
    size: 7, // px radius of packet circle
    speed: 320, // px per second
    maxHops: 6,
    color: getCssColor("--packet-fill"),
    borderColor: getCssColor("--packet-stroke"),
  },
  [RoutingStrategy.FLOOD]: {
    speed: 180, // px per second
    color: getCssColor("--broadcast-stroke"),
    opacity: 0.7,
  },
};

const AUTO_TRANSMIT = {
  minInterval: 700, // ms between transmissions
  maxInterval: 1700, // ms between transmissions
  batchSize: 4,
};

const BUTTONS = [
  {
    id: "send-direct",
    icon: "→",
    label: "Send Direct",
    title: "Transmit multiple unicast packets between client nodes",
    action: () => {
      transmitPacket({ strategy: RoutingStrategy.DIRECT });
      setTimeout(
        () => transmitPacket({ strategy: RoutingStrategy.DIRECT }),
        150,
      );
      setTimeout(
        () => transmitPacket({ strategy: RoutingStrategy.DIRECT }),
        300,
      );
    },
  },
  {
    id: "send-flood",
    icon: "➜",
    label: "Send Flood",
    title: "Transmit a broadcast packet to nearby nodes",
    action: () => transmitPacket({ strategy: RoutingStrategy.FLOOD }),
  },
  {
    id: "add-client",
    icon: "＋",
    label: "Add Client",
    title: "End-user node that sends and receives packets",
    action: () => addNode(NodeType.CLIENT),
  },
  {
    id: "add-repeater",
    icon: "⊕",
    label: "Add Repeater",
    title: "Relay node that forwards packets between clients",
    action: () => addNode(NodeType.REPEATER),
  },
  {
    id: "reset",
    icon: "↻",
    label: "Reset",
    title: "Reinitialize the network layout and restart the animation",
    action: () => resetNetwork(),
  },
];

const FPS_TARGET = isMobileDevice() ? 30 : 60;
const MIN_FRAME_DELAY = 1000 / FPS_TARGET;

const IS_DEBUG_MODE = window.location.search.includes("debug");

// --- STATE VARIABLES ---

let staticCanvas;
let staticCtx;
let dynamicCanvas;
let dynamicCtx;
let needsStaticRedraw = true;

let dpr = window.devicePixelRatio || 1;
let simWidth;
let simHeight;
let offsetX = 0;
let offsetY = 0;
let resizeTimeout;

let nodes = [];
let packets = [];
let broadcasts = [];
let seenBroadcasts = new Set();

let packetPool = createPool(newPacket);
let trailPool = createPool(newTrail);
let broadcastPool = createPool(newBroadcast);

let nodeState;
let unicastState;
let broadcastState;
let minNodeDistance;

let autoTransmitter = {
  nextTime: Date.now(),
  interval: 0,
};

let hoveredNode = null;
let clickedButton = null;

let animationRunning = true;
let animationFrame = null;
let lastFrameTime = 0;
let lastDrawTime = 0;
let drawTimes = [];

let debugInfoElement = null;

// --- UTILITY FUNCTIONS ---

function generateId() {
  return crypto.randomUUID();
}

function getDistance(a, b) {
  const dx = a.x - b.x;
  const dy = a.y - b.y;
  return Math.sqrt(dx * dx + dy * dy);
}

function getSquaredDistance(a, b) {
  const dx = a.x - b.x;
  const dy = a.y - b.y;
  return dx * dx + dy * dy;
}

function getRandomInt(min, max) {
  return Math.floor(Math.random() * (max - min + 1)) + min;
}

function isMobileDevice() {
  return (
    window.innerWidth <= 768 ||
    (navigator.maxTouchPoints > 0 &&
      /Android|iPhone|iPad|iPod|BlackBerry|IEMobile|Opera Mini/i.test(
        navigator.userAgent,
      ))
  );
}

function parseHsl(string) {
  if (!string.startsWith("hsl(") || !string.endsWith(")")) {
    throw new Error(`Invalid HSL string: ${string}`);
  }

  const [h, s, l] = string
    .slice(4, -1) // strip "hsl(" and ")"
    .split(",")
    .map((part) => parseFloat(part)); // parse and strip '%' implicitly

  return { h, s, l };
}

function getCssColor(varName) {
  const raw = getComputedStyle(document.documentElement)
    .getPropertyValue(varName)
    .trim();

  return parseHsl(raw);
}

function createColorCache() {
  const cache = new WeakMap();

  return function hsla(color, alpha) {
    if (alpha === undefined) {
      throw new Error("Alpha value must be explicitly provided");
    }

    let alphaMap = cache.get(color);
    if (!alphaMap) {
      alphaMap = new Map();
      cache.set(color, alphaMap);
    }

    if (!alphaMap.has(alpha)) {
      const hslaStr = `hsla(${color.h}, ${color.s}%, ${color.l}%, ${alpha})`;
      alphaMap.set(alpha, hslaStr);
    }

    return alphaMap.get(alpha);
  };
}

const getHsla = createColorCache();

// --- CORE SIMULATION FUNCTIONS ---

function createNode(type) {
  const config = getNodeConfig(type);
  if (!config) return null;

  const { size, hitbox, range, rangeVariance, color } = config;

  const node = {
    id: generateId(),
    type,
    x: 0,
    y: 0,
    size,
    hitbox,
    range: range + getRandomInt(-rangeVariance, rangeVariance),
    color,
  };

  return node;
}

function generateCoords(useGrid, col, row, cellW, cellH, radius) {
  if (useGrid) {
    return {
      x: col * cellW + cellW * (0.25 + Math.random() * 0.5),
      y: row * cellH + cellH * (0.25 + Math.random() * 0.5),
    };
  } else {
    return {
      x: getRandomInt(radius * 2, simWidth - radius * 2),
      y: getRandomInt(radius * 2, simHeight - radius * 2),
    };
  }
}

function isTooClose(x, y) {
  return nodes.some((n) => getDistance({ x, y }, n) < minNodeDistance);
}

function tryPlaceNode(node, useGrid, col, row, cellW, cellH) {
  // attempt placement up to 30 times
  for (let i = 0; i < 30; i++) {
    const { x, y } = generateCoords(
      useGrid,
      col,
      row,
      cellW,
      cellH,
      node.hitbox,
    );
    node.x = x;
    node.y = y;

    if (!isTooClose(node.x, node.y)) return true;
  }
  return false;
}

const layoutNodes = (type) => {
  const config = getNodeConfig(type);
  if (!config) return;

  const { count, useGrid } = config;

  const gridCols = useGrid ? Math.ceil(Math.sqrt(count)) : 0;
  const gridRows = useGrid ? Math.ceil(count / gridCols) : 0;
  const cellWidth = useGrid ? simWidth / gridCols : 0;
  const cellHeight = useGrid ? simHeight / gridRows : 0;

  let placed = 0;
  for (let i = 0; i < count; i++) {
    const node = createNode(type);
    const row = useGrid ? Math.floor(placed / gridCols) : null;
    const col = useGrid ? placed % gridCols : null;

    const success = tryPlaceNode(
      node,
      useGrid,
      col,
      row,
      cellWidth,
      cellHeight,
    );
    if (success) {
      nodes.push(node);
      placed++;
    }
  }
};

function getNodeConfig(type) {
  const config = nodeState[type];
  if (!config) {
    console.error(`Unknown node type: ${type}`);
    return null;
  }
  return config;
}

/**
 * Performs a breadth-first search to find the shortest valid route
 * from the source node to the target node, considering wireless range.
 *
 * - Direct client-to-client hops are allowed.
 * - Multi-hop paths (3+ nodes) must use only repeaters as intermediate hops.
 * - Returns a path as an array of node { id, x, y } objects, always including the source.
 * - If no valid route is found, returns a single-element array with only the source.
 *
 * @param {Object} source - The starting node.
 * @param {Object} target - The destination node.
 * @returns {Array} Array of hops (each with id, x, y).
 */
function findRoute(source, target) {
  const visited = new Set();
  const queue = [[{ id: source.id, x: source.x, y: source.y }]];

  while (queue.length > 0) {
    const path = queue.shift();
    const last = path[path.length - 1];

    if (last.id === target.id) {
      // Validate intermediate hops (must be repeaters if path length > 2)
      if (
        path.length <= 2 ||
        path.slice(1, -1).every((hop) => {
          const node = nodes.find((n) => n.id === hop.id);
          return node && node.type === NodeType.REPEATER;
        })
      ) {
        return path;
      }
      continue;
    }

    if (visited.has(last.id)) continue;
    visited.add(last.id);

    const currentNode = nodes.find((n) => n.id === last.id);
    if (!currentNode) continue;

    const neighbors = currentNode.neighbors.filter(
      (other) => !visited.has(other.id),
    );

    for (const neighbor of neighbors) {
      queue.push([...path, { id: neighbor.id, x: neighbor.x, y: neighbor.y }]);
    }
  }

  // No valid route found
  return [{ id: source.id, x: source.x, y: source.y }];
}

function createPool(factory) {
  const pool = [];

  return {
    acquire: () => pool.pop() || factory(),
    release: (obj) => {
      // Reset object state before reuse
      if (typeof obj.reset === "function") obj.reset();
      pool.push(obj);
    },
    clear: () => {
      pool.length = 0;
    },
  };
}

function newTrail() {
  return {
    points: [], // circular buffer
    max: 8,
    index: 0,
    reset() {
      this.points.length = 0;
      this.index = 0;
    },
  };
}

function acquireTrail() {
  return trailPool.acquire();
}

function releaseTrail(trail) {
  trailPool.release(trail);
}

function addToTrail(trail, point) {
  if (trail.points.length < trail.max) {
    trail.points.push(point);
  } else {
    trail.points[trail.index] = point;
    trail.index = (trail.index + 1) % trail.max;
  }
}

function newPacket() {
  return {
    id: "",
    strategy: RoutingStrategy.DIRECT,
    sourceId: "",
    targetId: "",
    x: 0,
    y: 0,
    size: 0,
    route: [],
    hopIndex: 0,
    delivered: false,
    progress: 0,
    trail: null,
    reset() {
      this.id = "";
      this.sourceId = "";
      this.targetId = "";
      this.x = 0;
      this.y = 0;
      this.size = 0;
      this.route.length = 0;
      this.hopIndex = 0;
      this.delivered = false;
      this.progress = 0;
      if (this.trail) {
        releaseTrail(this.trail);
        this.trail = null;
      }
    },
  };
}

function acquirePacket() {
  const packet = packetPool.acquire();
  packet.id = generateId();
  return packet;
}

function releasePacket(packet) {
  packetPool.release(packet);
}

function createDirectPacket(source, target) {
  const route = findRoute(source, target);

  if (
    route.length === 1 || // no valid path
    route.length - 1 > unicastState.maxHops // too many hops
  ) {
    return null;
  }

  const packet = acquirePacket();

  Object.assign(packet, {
    sourceId: source.id,
    targetId: target.id,
    x: source.x,
    y: source.y,
    size: unicastState.size,
    route,
    trail: acquireTrail(),
  });

  return packet;
}

function newBroadcast() {
  return {
    id: "",
    floodId: "",
    sourceId: "",
    x: 0,
    y: 0,
    radius: 0,
    range: 0,
    speed: 0,
    opacity: 0,
    reset() {
      this.id = "";
      this.floodId = "";
      this.sourceId = "";
      this.x = 0;
      this.y = 0;
      this.radius = 0;
      this.range = 0;
      this.speed = 0;
      this.opacity = 0;
    },
  };
}

function acquireBroadcast() {
  const broadcast = broadcastPool.acquire();
  broadcast.id = generateId();
  return broadcast;
}

function releaseBroadcast(broadcast) {
  broadcastPool.release(broadcast);
}

function createBroadcast(source, originFloodId = null) {
  const floodId = originFloodId || generateId();
  const broadcast = acquireBroadcast();

  Object.assign(broadcast, {
    floodId,
    sourceId: source.id,
    x: source.x,
    y: source.y,
    radius: 0,
    range: source.range,
    speed: broadcastState.speed,
    opacity: broadcastState.opacity,
  });

  return broadcast;
}

const addNode = (type) => {
  const node = createNode(type);
  const success = tryPlaceNode(node, false); // no grid for manual adds
  if (success) {
    nodes.push(node);
    computeNeighbors();
    needsStaticRedraw = true;
  }
};

function pickRandomClient(excludeId = null) {
  const clients = nodes.filter(
    (n) => n.type === NodeType.CLIENT && n.id !== excludeId,
  );
  return clients[Math.floor(Math.random() * clients.length)];
}

function computeNeighbors() {
  for (const node of nodes) {
    node.neighbors = [];
    node.nearClients = [];
    node.farClients = [];

    for (const other of nodes) {
      if (node.id === other.id) continue;

      const distSq = getSquaredDistance(node, other);
      const inRange = distSq <= node.range * node.range;

      if (inRange) {
        node.neighbors.push(other);
        if (other.type === NodeType.CLIENT) {
          node.nearClients.push(other);
        }
      } else if (other.type === NodeType.CLIENT) {
        node.farClients.push(other);
      }
    }
  }
}

function tryMultiHopRoute(source, candidates) {
  for (let i = 0; i < 3; i++) {
    const target = candidates[Math.floor(Math.random() * candidates.length)];
    const packet = createDirectPacket(source, target);
    if (!packet) continue;

    // Prefer longer paths
    if (packet.route.length > 3) return packet;

    // Accept shorter multi-hop (1 repeater) routes 50% of the time,
    // but otherwise keep looking in hopes of finding a longer path
    if (packet.route.length > 2 && Math.random() < 0.5) return packet;
  }
  return null;
}

function tryAnyRoute(source, candidates) {
  for (const target of candidates) {
    const packet = createDirectPacket(source, target);
    if (packet) return packet;
  }
  return null;
}

function findAestheticRoute(source) {
  const farClients = source.farClients;
  const nearClients = source.nearClients;

  // Prefer multi-hop routes (80% chance)
  if (farClients.length > 0 && Math.random() < 0.8) {
    const packet = tryMultiHopRoute(source, farClients);
    if (packet) return packet;
  }

  // Try direct delivery to a nearby client
  if (nearClients.length > 0) {
    const target = nearClients[Math.floor(Math.random() * nearClients.length)];
    const packet = createDirectPacket(source, target);
    if (packet) return packet;
  }

  // Fallback to *any* valid route to a distant client
  if (farClients.length > 0) {
    const packet = tryAnyRoute(source, farClients);
    if (packet) return packet;
  }

  return null;
}

function transmitPacket({ id = null, strategy }) {
  const source = id ? nodes.find((n) => n.id === id) : pickRandomClient();
  if (!source) return;

  if (strategy === RoutingStrategy.DIRECT) {
    const packet = findAestheticRoute(source);
    if (packet) packets.push(packet);
  } else if (strategy === RoutingStrategy.FLOOD) {
    const broadcast = createBroadcast(source);
    seenBroadcasts.add(`${broadcast.floodId}-${source.id}`);
    broadcasts.push(broadcast);
  } else {
    console.warn("Unknown routing strategy:", strategy);
  }
}

const resetNetwork = () => {
  cancelAnimationFrame(animationFrame);
  resizeCanvases();
  applyScaling();
  initNetwork();
  animate(performance.now());
};

function scaleForMobile(value) {
  return isMobileDevice() ? Math.round(value * (3 / 5)) : value;
}

// Scale simulation parameters based on device size and pixel density
const applyScaling = () => {
  nodeState = {};
  Object.entries(NODE_DEFAULT).forEach(([type, def]) => {
    nodeState[type] = {
      ...def,
      count: scaleForMobile(def.count),
      size: scaleForMobile(def.size),
      hitbox: scaleForMobile(def.hitbox),
      range: scaleForMobile(def.range),
      rangeVariance: scaleForMobile(def.rangeVariance),
    };
  });

  unicastState = {
    ...PACKET_DEFAULT.unicast,
    size: scaleForMobile(PACKET_DEFAULT.unicast.size),
    speed: scaleForMobile(PACKET_DEFAULT.unicast.speed),
  };

  broadcastState = {
    ...PACKET_DEFAULT.broadcast,
    speed: scaleForMobile(PACKET_DEFAULT.broadcast.speed),
  };

  minNodeDistance = scaleForMobile(70);
};

function initNetwork(clientCount = null, repeaterCount = null) {
  // Reset simulation state
  nodes.length = 0;
  packets.length = 0;
  broadcasts.length = 0;
  seenBroadcasts.clear();
  hoveredNode = null;

  broadcastPool.clear();
  packetPool.clear();
  trailPool.clear();

  // Use current node config counts unless overrides are provided
  const clientCfg = getNodeConfig(NodeType.CLIENT);
  const repeaterCfg = getNodeConfig(NodeType.REPEATER);

  const clientCountFinal = clientCount ?? clientCfg.count;
  const repeaterCountFinal = repeaterCount ?? repeaterCfg.count;

  clientCfg.count = clientCountFinal;
  repeaterCfg.count = repeaterCountFinal;

  // Place repeaters first to give them the best grid spacing
  layoutNodes(NodeType.REPEATER);
  layoutNodes(NodeType.CLIENT);

  computeNeighbors();
  autoTransmitter.nextTime = Date.now();
}

// --- DRAWING FUNCTIONS ---

// Draw transmission range for nodes
const drawNodeRanges = (ctx) => {
  nodes.forEach((node) => {
    ctx.beginPath();
    ctx.arc(node.x, node.y, node.range, 0, Math.PI * 2);

    const isHovered = hoveredNode && node.id === hoveredNode.id;

    ctx.strokeStyle = getHsla(node.color, isHovered ? 0.5 : 0.1);
    ctx.lineWidth = 1;
    ctx.stroke();
  });
};

const drawBroadcasts = (ctx) => {
  broadcasts.forEach((broadcast) => {
    ctx.beginPath();
    ctx.arc(broadcast.x, broadcast.y, broadcast.radius, 0, Math.PI * 2);
    ctx.strokeStyle = getHsla(broadcastState.color, broadcastState.opacity);
    ctx.lineWidth = 2;
    ctx.stroke();
  });
};

// Draw packet paths (faint lines showing the route)
const drawPacketRoutes = (ctx) => {
  const routeColor = getHsla(unicastState.color, 0.5);
  packets.forEach((packet) => {
    if (packet.strategy !== RoutingStrategy.DIRECT) return;
    if (packet.delivered) return;

    ctx.beginPath();
    ctx.setLineDash([3, 3]);
    ctx.strokeStyle = routeColor;
    ctx.lineWidth = 1;

    const route = packet.route;
    if (!route || route.length < 2) return;
    ctx.moveTo(route[0].x, route[0].y);

    for (let i = 1; i < route.length; i++) {
      ctx.lineTo(route[i].x, route[i].y);
    }

    ctx.stroke();
    ctx.setLineDash([]); // Reset line dash
  });
};

function forEachTrailPoint(trail, callback) {
  const { points, index } = trail;
  const len = points.length;

  for (let i = 0; i < len; i++) {
    const realIndex = (index + i) % len;
    callback(points[realIndex], i);
  }
}

// Draw trails behind packets
const drawPacketTrails = (ctx) => {
  packets.forEach((packet) => {
    if (packet.strategy !== RoutingStrategy.DIRECT) return;

    const { trail } = packet;
    const { points } = trail;
    if (!points || points.length < 2) return;

    let first, last;

    ctx.beginPath();
    forEachTrailPoint(trail, (point, i) => {
      if (i === 0) {
        ctx.moveTo(point.x, point.y);
        first = point;
      } else {
        ctx.lineTo(point.x, point.y);
      }
      last = point;
    });

    const gradient = ctx.createLinearGradient(first.x, first.y, last.x, last.y);
    gradient.addColorStop(0, getHsla(unicastState.color, 0));
    gradient.addColorStop(1, getHsla(unicastState.color, 0.5));

    ctx.strokeStyle = gradient;
    ctx.lineWidth = 3;
    ctx.stroke();
  });
};

const drawHexagon = (
  ctx,
  { x, y, size, fillColor, borderColor, lineWidth = 1.5 },
) => {
  const numberOfSides = 6;
  const a = (Math.PI * 2) / numberOfSides;

  ctx.beginPath();
  ctx.moveTo(
    x + size * Math.cos(Math.PI / 2),
    y + size * Math.sin(Math.PI / 2),
  );

  for (let i = 1; i <= numberOfSides; i++) {
    const angle = Math.PI / 2 + a * i;
    ctx.lineTo(x + size * Math.cos(angle), y + size * Math.sin(angle));
  }

  ctx.closePath();
  ctx.fillStyle = getHsla(fillColor, 1);
  ctx.fill();
  ctx.strokeStyle = getHsla(borderColor, 1);
  ctx.lineWidth = lineWidth;
  ctx.stroke();
};

const drawNodes = (ctx) => {
  nodes.forEach((node) => {
    const config = getNodeConfig(node.type);
    if (!config) return;

    const isHovered = hoveredNode && node.id === hoveredNode.id;

    drawHexagon(ctx, {
      x: node.x,
      y: node.y,
      size: node.size,
      fillColor: config.color,
      borderColor: config.borderColor,
      lineWidth: isHovered ? 3 : 1.5,
    });
  });
};

const drawPackets = (ctx) => {
  packets.forEach((packet) => {
    if (packet.strategy !== RoutingStrategy.DIRECT) return;

    if (packet.delivered) {
      // Draw delivery effect (growing pulse)
      const easedProgress = Math.pow(packet.progress, 0.5);
      const radius = packet.size + easedProgress * 2 * packet.size;

      ctx.beginPath();
      ctx.arc(packet.x, packet.y, radius, 0, Math.PI * 2);
      ctx.fillStyle = getHsla(unicastState.color, 1 - easedProgress);
      ctx.fill();
    }

    // Draw packet (circle)
    ctx.beginPath();
    ctx.arc(packet.x, packet.y, packet.size, 0, Math.PI * 2);
    ctx.fillStyle = getHsla(unicastState.color, 1);
    ctx.fill();
    ctx.strokeStyle = getHsla(unicastState.borderColor, 0.6);
    ctx.lineWidth = 1;
    ctx.stroke();
  });
};

function renderStaticLayer() {
  staticCtx.clearRect(0, 0, staticCanvas.width, staticCanvas.height);
  staticCtx.save();
  staticCtx.translate(offsetX, offsetY);

  drawNodeRanges(staticCtx);
  drawNodes(staticCtx);

  staticCtx.restore();
}

function renderDynamicLayer() {
  dynamicCtx.clearRect(0, 0, dynamicCanvas.width, dynamicCanvas.height);
  dynamicCtx.save();
  dynamicCtx.translate(offsetX, offsetY);

  drawBroadcasts(dynamicCtx);
  drawPacketRoutes(dynamicCtx);
  drawPacketTrails(dynamicCtx);
  drawPackets(dynamicCtx);

  dynamicCtx.restore();
}

function renderFrame() {
  if (needsStaticRedraw) {
    renderStaticLayer();
    needsStaticRedraw = false;
  }
  renderDynamicLayer();
}

// --- SIMULATION UPDATE FUNCTIONS ---

function updatePacketDeliveryEffect(packet, deltaTime) {
  const duration = 0.6; // seconds
  packet.progress += deltaTime / duration;
  return packet.progress >= 1;
}

/**
 * Returns a unit (normalized) direction vector pointing from `from` to `to`.
 *
 * The result is an object `{ x, y }` where both components range from -1 to 1.
 * If the points are the same, returns `{ x: 0, y: 0 }`.
 *
 * @param {Object} from - Starting point with { x, y }.
 * @param {Object} to - Destination point with { x, y }.
 * @returns {Object} Normalized direction vector { x, y }.
 */
function getUnitVector(from, to) {
  const dx = to.x - from.x;
  const dy = to.y - from.y;
  const dist = getDistance(from, to);
  return dist === 0 ? { x: 0, y: 0 } : { x: dx / dist, y: dy / dist };
}

function movePacketAlongRoute(packet, deltaTime) {
  const next = packet.route[packet.hopIndex + 1];
  if (!next) return;

  const now = performance.now();
  addToTrail(packet.trail, { x: packet.x, y: packet.y, time: now });

  const distToNext = getDistance(packet, next);
  const moveDist = unicastState.speed * deltaTime;

  if (moveDist >= distToNext) {
    // Reached next hop
    packet.x = next.x;
    packet.y = next.y;
    packet.hopIndex++;

    // Recycle the trail (whether delivered or continuing)
    releaseTrail(packet.trail);
    packet.trail = acquireTrail();

    if (packet.hopIndex === packet.route.length - 1) {
      packet.delivered = true;
      packet.progress = 0;
    }
  } else {
    // Move toward next hop
    const direction = getUnitVector(packet, next);
    packet.x += direction.x * moveDist;
    packet.y += direction.y * moveDist;
  }
}

function updatePackets(deltaTime) {
  for (let i = packets.length - 1; i >= 0; i--) {
    const packet = packets[i];
    if (packet.strategy !== RoutingStrategy.DIRECT) continue;

    if (packet.delivered) {
      if (updatePacketDeliveryEffect(packet, deltaTime)) {
        packets.splice(i, 1);
        releasePacket(packet);
      }
    } else {
      movePacketAlongRoute(packet, deltaTime);
    }
  }
}

function processCollision(broadcast, node) {
  const key = `${broadcast.floodId}-${node.id}`;
  if (node.id === broadcast.sourceId || seenBroadcasts.has(key)) {
    return false;
  }

  const distSq = getSquaredDistance(broadcast, node);
  const minR = broadcast.radius - node.hitbox;
  const maxR = broadcast.radius + node.hitbox;
  const hit = distSq >= minR * minR && distSq <= maxR * maxR;

  if (hit) {
    seenBroadcasts.add(key);
    if (node.type === NodeType.REPEATER) {
      broadcasts.push(createBroadcast(node, broadcast.floodId));
    }
  }

  return hit;
}

function updateBroadcasts(deltaTime) {
  for (let i = broadcasts.length - 1; i >= 0; i--) {
    const broadcast = broadcasts[i];
    broadcast.radius += broadcast.speed * deltaTime;
    broadcast.opacity =
      broadcastState.opacity * (1 - broadcast.radius / broadcast.range);

    const source = nodes.find((n) => n.id === broadcast.sourceId);
    if (source) {
      for (const node of source.neighbors) {
        processCollision(broadcast, node);
      }
    }

    const expired = broadcast.radius >= broadcast.range;
    if (!expired) continue;

    const { floodId } = broadcast;
    broadcasts.splice(i, 1);
    releaseBroadcast(broadcast);

    const stillActive = broadcasts.some((b) => b.floodId === floodId);

    if (!stillActive) {
      for (const key of seenBroadcasts) {
        if (key.startsWith(`${floodId}-`)) {
          seenBroadcasts.delete(key);
        }
      }
    }
  }
}

const updateFPS = (timestamp, cpuMs = 0) => {
  if (!IS_DEBUG_MODE) return;

  if (timestamp - lastDrawTime >= MIN_FRAME_DELAY * 0.9) {
    drawTimes.push(timestamp);
    lastDrawTime = timestamp;

    while (drawTimes.length > 0 && timestamp - drawTimes[0] > 1000) {
      drawTimes.shift();
    }

    const fps = drawTimes.length;
    const cpu = cpuMs.toFixed(1).padStart(5);
    debugInfoElement.textContent = `${fps} FPS | ${cpu} ms`;
  }
};

function autoTransmitPackets() {
  const now = Date.now();
  if (now < autoTransmitter.nextTime) return;

  const clients = nodes.filter((n) => n.type === NodeType.CLIENT);
  if (!clients.length) return;

  const { minInterval, maxInterval, batchSize } = AUTO_TRANSMIT;
  for (let i = 0; i < batchSize; i++) {
    setTimeout(() => {
      const source = clients[Math.floor(Math.random() * clients.length)];
      const strategy =
        Math.random() < 0.05 ? RoutingStrategy.FLOOD : RoutingStrategy.DIRECT;
      transmitPacket({ id: source.id, strategy });
    }, i * 120);
  }

  autoTransmitter.interval = getRandomInt(minInterval, maxInterval);
  autoTransmitter.nextTime = now + autoTransmitter.interval;
}

function schedulePacketTransmission() {
  const idleCallback =
    window.requestIdleCallback ||
    ((cb) => setTimeout(() => cb({ timeRemaining: () => 0 }), 200));

  idleCallback(() => {
    if (nodes.length && animationRunning) autoTransmitPackets();
    schedulePacketTransmission(); // loop
  });
}

// --- UI / EVENT FUNCTIONS ---

// Resize canvases to match container with scaling
function resizeCanvases() {
  const container = staticCanvas.parentElement;
  const newWidth = container.offsetWidth;
  const newHeight = container.offsetHeight;

  [staticCanvas, dynamicCanvas].forEach((canvas) => {
    canvas.width = newWidth * dpr;
    canvas.height = newHeight * dpr;
    canvas.style.width = newWidth + "px";
    canvas.style.height = newHeight + "px";
  });

  staticCtx.setTransform(1, 0, 0, 1, 0, 0);
  dynamicCtx.setTransform(1, 0, 0, 1, 0, 0);
  staticCtx.scale(dpr, dpr);
  dynamicCtx.scale(dpr, dpr);

  simWidth = newWidth;
  simHeight = newHeight;

  offsetX = (newWidth - simWidth) / 2;
  offsetY = (newHeight - simHeight) / 2;

  needsStaticRedraw = true;
}

function setupResizeListener() {
  window.addEventListener(
    "resize",
    () => {
      clearTimeout(resizeTimeout);

      resizeTimeout = setTimeout(() => {
        const newDpr = window.devicePixelRatio || 1;
        const container = staticCanvas.parentElement;
        const width = container.offsetWidth;
        const height = container.offsetHeight;

        const canvasSizeChanged =
          simWidth !== width || simHeight !== height || dpr !== newDpr;

        if (canvasSizeChanged) {
          dpr = newDpr;
          resetNetwork();
        }
      }, 250);
    },
    { passive: true },
  );
}

function setupVisibilityObserver() {
  if (!("IntersectionObserver" in window)) return;

  const observer = new IntersectionObserver(
    (entries) => {
      entries.forEach((entry) => {
        if (entry.isIntersecting) {
          if (!animationRunning) {
            animationRunning = true;
            animate(performance.now());
          }
        } else {
          if (animationRunning) {
            animationRunning = false;
            cancelAnimationFrame(animationFrame);
          }
        }
      });
    },
    { threshold: 0.01 },
  );

  const target = document.querySelector(".hero-section");
  observer.observe(target);
}

function setupButtonListeners() {
  BUTTONS.forEach(({ id, action }) => {
    const button = document.getElementById(id);
    if (button && action) {
      button.addEventListener("pointerdown", (e) => {
        e.preventDefault();
        clickedButton = button;
        button.classList.add("clicked");
        action();
      });

      button.addEventListener("pointerup", () => {
        if (clickedButton) {
          clickedButton.classList.remove("clicked");
          clickedButton = null;
        }
      });

      button.addEventListener("pointerleave", () => {
        if (clickedButton) {
          clickedButton.classList.remove("clicked");
          clickedButton = null;
        }
      });
    }
  });
}

function setupNodeHoverListener(canvas) {
  canvas.addEventListener(
    "pointermove",
    (e) => {
      const rect = canvas.getBoundingClientRect();
      const x = e.clientX - rect.left;
      const y = e.clientY - rect.top;

      const newHoveredNode = nodes.find(
        (n) => getSquaredDistance(n, { x, y }) <= n.size * n.size,
      );

      if (newHoveredNode?.id !== hoveredNode?.id) {
        hoveredNode = newHoveredNode;
        needsStaticRedraw = true;
      }
    },
    { passive: true },
  );

  canvas.addEventListener(
    "pointerleave",
    () => {
      hoveredNode = null;
      needsStaticRedraw = true;
    },
    { passive: true },
  );
}

function setupNodeClickListener(canvas) {
  canvas.addEventListener("pointerdown", (e) => {
    const rect = canvas.getBoundingClientRect();
    const x = e.clientX - rect.left;
    const y = e.clientY - rect.top;

    const clickedNode = nodes.find(
      (n) => getSquaredDistance(n, { x, y }) <= n.size * n.size,
    );

    if (clickedNode) {
      switch (clickedNode.type) {
        case NodeType.CLIENT:
          transmitPacket({
            id: clickedNode.id,
            strategy: RoutingStrategy.DIRECT,
          });
          break;

        case NodeType.REPEATER:
          transmitPacket({
            id: clickedNode.id,
            strategy: RoutingStrategy.FLOOD,
          });
          break;
      }
    }

    hoveredNode = clickedNode;
    needsStaticRedraw = true;
  });
}

function setupEventListeners() {
  setupResizeListener();
  setupVisibilityObserver();
  setupButtonListeners();
  setupNodeHoverListener(dynamicCanvas);
  setupNodeClickListener(dynamicCanvas);
}

// Animation loop
const animate = (timestamp) => {
  if (!animationRunning) return;

  if (timestamp - lastFrameTime < MIN_FRAME_DELAY * 0.9) {
    animationFrame = requestAnimationFrame(animate);
    return;
  }

  const cpuStart = performance.now(); // START timing

  const deltaTime = (timestamp - lastFrameTime) / 1000; // seconds
  lastFrameTime = timestamp;

  updatePackets(deltaTime);
  updateBroadcasts(deltaTime);
  renderFrame();

  const cpuDuration = performance.now() - cpuStart; // END timing
  updateFPS(timestamp, cpuDuration);

  animationFrame = requestAnimationFrame(animate);
};

// --- INITIALIZATION ---

const init = () => {
  staticCanvas = document.getElementById("static-canvas");
  dynamicCanvas = document.getElementById("dynamic-canvas");

  staticCtx = staticCanvas.getContext("2d");
  dynamicCtx = dynamicCanvas.getContext("2d");

  const controlsContainer = document.getElementById("controls-container");

  BUTTONS.forEach(({ id, icon, label, title }) => {
    const [iconSymbol, labelText] = [icon, label];
    const button = document.createElement("button");
    button.id = id;
    button.innerHTML = `<span class="icon">${iconSymbol}</span> ${labelText}`;
    if (title) button.title = title;
    controlsContainer.appendChild(button);
  });

  if (IS_DEBUG_MODE) {
    debugInfoElement = document.createElement("div");
    debugInfoElement.id = "debug-info";
    document.body.appendChild(debugInfoElement);
  }

  resetNetwork();
  schedulePacketTransmission();
  setupEventListeners();
};

init();
