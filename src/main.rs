// main.rs
use std::io::{self, Write};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};
use std::thread;
use std::collections::{HashSet, HashMap, VecDeque};
use sysinfo::{Pid, System};
use winapi::shared::minwindef::{LPCVOID, LPVOID};
use winapi::um::memoryapi::{VirtualQueryEx, ReadProcessMemory};
use winapi::um::processthreadsapi::OpenProcess;
use winapi::um::winnt::{
    HANDLE, MEMORY_BASIC_INFORMATION, PROCESS_QUERY_INFORMATION, PROCESS_VM_READ,
    PAGE_READWRITE,
};
use std::mem;
use std::fs::{self, OpenOptions};
use std::path::{Path, PathBuf};
use std::sync::mpsc;
use std::fs::metadata;
use std::io::Seek;
use std::io::SeekFrom;

use aho_corasick::AhoCorasick;
use chrono::Local;
use lazy_static::lazy_static;
use regex::Regex;
use egui::{Color32, Id, ScrollArea, RichText, Window, ComboBox, Slider, TextEdit, TextStyle, Layout, Align};
use eframe::egui;

use serde::{Serialize, Deserialize};
use rodio::{OutputStream, Sink, source::{SineWave, Source}, Decoder};
use serde_json;
use rfd::FileDialog;

/// A predefined list of chat prefixes to search for.
/// This mimics the `CHAT_CHANNELS` dictionary from the Python script.
const CHAT_PREFIXES: &[&str] = &[
    "[Say]", "[World]", "[Other]", "Adquiriu ", "[Party]", "[Whisper]", "[Guild]",
    "[Combat]", "[Trade]", "[Yell]", "[Broadcas]", "[Announce]",
    "[System]",
];

/// The name of the process to scan.
const PROCESS_NAME: &str = "GrandFantasia.exe";
/// The name of the settings file.
const SETTINGS_FILE: &str = "chat_logger_settings.json";

/// Finds all PIDs of a process by its executable name.
/// Returns a `Result` with a `Vec<Pid>` if found, or an error string otherwise.
fn find_all_pids_by_name(process_name: &str) -> Result<Vec<(Pid, String)>, String> {
    let mut system = System::new();
    system.refresh_processes();

    let pids: Vec<(Pid, String)> = system.processes()
        .iter()
        .filter(|(_, process)| process.name().eq_ignore_ascii_case(process_name))
        .map(|(pid, process)| (*pid, process.name().to_string()))
        .collect();

    if pids.is_empty() {
        Err(format!("Process '{}' not found.", process_name))
    } else {
        Ok(pids)
    }
}

/// Reads a zero-terminated string from a process's memory.
fn read_zero_terminated_string(process_handle: HANDLE, address: usize) -> String {
    let mut buffer = Vec::new();
    let mut current_address = address;
    let mut chunk = [0u8; 256];

    loop {
        let mut bytes_read = 0;
        let read_result = unsafe {
            ReadProcessMemory(
                process_handle,
                current_address as LPCVOID,
                chunk.as_mut_ptr() as LPVOID,
                chunk.len(),
                &mut bytes_read,
            )
        };

        if read_result == 0 || bytes_read == 0 {
            break;
        }

        let slice = &chunk[..bytes_read as usize];
        if let Some(pos) = slice.iter().position(|&x| x == 0) {
            buffer.extend_from_slice(&slice[..pos]);
            break;
        } else {
            buffer.extend_from_slice(slice);
            current_address += bytes_read as usize;
        }

        if buffer.len() > 4096 {
            break;
        }
    }
    String::from_utf8_lossy(&buffer).to_string()
}

// A simple message struct to send between the scanner and the UI thread.
struct ChatMessage {
    prefix: String,
    content: String,
    address: usize,
    sub_channel: Option<String>,
    color: Color32,
    do_ding: bool,
    timestamp: String,
    // Add raw data for the damage analyzer plugin
    raw_content: Option<String>,
}

#[derive(PartialEq, Debug, Clone, Copy, Hash, Eq, Serialize, Deserialize)]
enum ChatChannel {
    All,
    Say,
    World,
    Other,
    Items,
    Party,
    Whisper,
    Guild,
    Combat,
    Trade,
    Yell,
    Broadcast,
    Announce,
    System,
}

impl ChatChannel {
    fn all() -> Vec<Self> {
        vec![
            ChatChannel::All,
            ChatChannel::Say,
            ChatChannel::World,
            ChatChannel::Other,
            ChatChannel::Items,
            ChatChannel::Party,
            ChatChannel::Whisper,
            ChatChannel::Guild,
            ChatChannel::Combat,
            ChatChannel::Trade,
            ChatChannel::Yell,
            ChatChannel::Broadcast,
            ChatChannel::Announce,
            ChatChannel::System,
        ]
    }
    
    fn from_prefix(prefix: &str) -> Option<Self> {
        match prefix {
            "[Say]" => Some(ChatChannel::Say),
            "[World]" => Some(ChatChannel::World),
            "[Other]" => Some(ChatChannel::Other),
            "Adquiriu " => Some(ChatChannel::Items),
            "[Party]" => Some(ChatChannel::Party),
            "[Whisper]" => Some(ChatChannel::Whisper),
            "[Guild]" => Some(ChatChannel::Guild),
            "[Combat]" => Some(ChatChannel::Combat),
            "[Trade]" => Some(ChatChannel::Trade),
            "[Yell]" => Some(ChatChannel::Yell),
            "[Broadcas]" => Some(ChatChannel::Broadcast),
            "[Announce]" => Some(ChatChannel::Announce),
            "[System]" => Some(ChatChannel::System),
            _ => None,
        }
    }

    fn to_string(&self) -> String {
        match self {
            ChatChannel::All => "All".to_string(),
            ChatChannel::Say => "Say".to_string(),
            ChatChannel::World => "World".to_string(),
            ChatChannel::Other => "Other".to_string(),
            ChatChannel::Items => "Items".to_string(),
            ChatChannel::Party => "Party".to_string(),
            ChatChannel::Whisper => "Whisper".to_string(),
            ChatChannel::Guild => "Guild".to_string(),
            ChatChannel::Combat => "Combat".to_string(),
            ChatChannel::Trade => "Trade".to_string(),
            ChatChannel::Yell => "Yell".to_string(),
            ChatChannel::Broadcast => "Broadcast".to_string(),
            ChatChannel::Announce => "Announce".to_string(),
            ChatChannel::System => "System".to_string(),
        }
    }
}

// A simple struct to define sub-channels.
struct SubChannel {
    name: &'static str,
    regex: Regex,
}

lazy_static! {
    static ref SUB_CHANNELS: HashMap<ChatChannel, Vec<SubChannel>> = {
        let mut m = HashMap::new();
        m.insert(ChatChannel::Other, vec![
            SubChannel { name: "EXP", regex: Regex::new(r"\b(\d+ XP|experience gained)\b").unwrap() },
            SubChannel { name: "Gold", regex: Regex::new(r"\b(Acquired \d+ (Gold|Silver|Copper))\b").unwrap() },
            SubChannel { name: "EXP Special", regex: Regex::new(r"\b(Gained \d+ specialization EXP)\b").unwrap() },
            SubChannel { name: "Buffs", regex: Regex::new(r"(?:You have entered|You have left) \[.*\] state\.").unwrap() },
        ]);
        m.insert(ChatChannel::World, vec![
            SubChannel { name: "World Boss Defeated", regex: Regex::new(r"has defeated").unwrap() },
            SubChannel { name: "World Boss Appeared", regex: Regex::new(r"(has appeared|has been spotted|Urgent report|News Flash|Warning!)").unwrap() },
        ]);
        m.insert(ChatChannel::Combat, vec![
            SubChannel { name: "Heals", regex: Regex::new(r"heals .* for \d+ HP").unwrap() },
            SubChannel { name: "Mana", regex: Regex::new(r"(restores .* for \d+ MP|saps .* for \d+ MP)").unwrap() },
            SubChannel { name: "Combat Damage Skill", regex: Regex::new(r"attacks .* for \d+ HP").unwrap() },
            SubChannel { name: "Combat Damage Normal", regex: Regex::new(r"sustained \d+ damage").unwrap() },
            SubChannel { name: "Combat Player Hurt", regex: Regex::new(r"You are hurt by \d+").unwrap() },
        ]);
        m.insert(ChatChannel::System, vec![
            SubChannel { name: "Mount Equipment", regex: Regex::new(r"received \d+ experience").unwrap() },
            SubChannel { name: "Mastery Equipment", regex: Regex::new(r"Mastery equipment receives \d+ experience").unwrap() },
        ]);
        m
    };
    static ref DURATION_REGEX: Regex = Regex::new(r"in (\d+\.?\d*)ms").unwrap();
    static ref GOLD_REGEX: Regex = Regex::new(r"Acquired \d+ (Gold|Silver|Copper)").unwrap();
    static ref ITEM_REGEX: Regex = Regex::new(r"Adquiriu ").unwrap();
    static ref COMBAT_SKILL_REGEX: Regex = Regex::new(r"\[Combat\]: (.*) attacks (.*) for (\d+) HP").unwrap();
    static ref COMBAT_NORMAL_REGEX: Regex = Regex::new(r"\[Combat\]: You sustained (\d+) damage").unwrap();
    static ref COMBAT_NUMBER_REGEX: Regex = Regex::new(r"(\d+)( HP| damage)").unwrap();
    static ref EXP_REGEX: Regex = Regex::new(r"Gained (\d+) experience points\.").unwrap();
    static ref EXP_SPECIAL_REGEX: Regex = Regex::new(r"Gained (\d+) specialization EXP\.").unwrap();
    static ref MOUNT_EXP_REGEX: Regex = Regex::new(r"received (\d+) experience").unwrap();
    static ref MASTERY_EXP_REGEX: Regex = Regex::new(r"Mastery equipment receives (\d+) experience").unwrap();
}

#[derive(PartialEq, Clone, Debug, Serialize, Deserialize)]
struct ChannelGroup {
    name: String,
    channels: HashSet<ChatChannel>,
    excluded_subchannels: HashSet<String>,
}

// Enum to define timestamp format options for the UI.
#[derive(PartialEq, Clone, Copy, Debug, Serialize, Deserialize)]
enum TimestampFormat {
    Full,
    OnlyTime,
    Short,
    None,
}

impl TimestampFormat {
    fn to_string(&self) -> String {
        match self {
            TimestampFormat::Full => "Full (YYYY-MM-DD hh:mm:ss)".to_string(),
            TimestampFormat::OnlyTime => "Only Time (hh:mm:ss)".to_string(),
            TimestampFormat::Short => "Short (hh:mm)".to_string(),
            TimestampFormat::None => "None".to_string(),
        }
    }
    fn format_timestamp(&self, timestamp: &chrono::DateTime<Local>) -> String {
        match self {
            TimestampFormat::Full => timestamp.format("%Y-%m-%d %H:%M:%S").to_string(),
            TimestampFormat::OnlyTime => timestamp.format("%H:%M:%S").to_string(),
            TimestampFormat::Short => timestamp.format("%H:%M").to_string(),
            TimestampFormat::None => "".to_string(),
        }
    }
}

// New data structures for the damage analyzer plugin
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
struct DamageEntry {
    damage: u32,
    timestamp: u64,
}

#[derive(Debug, Clone, Default)]
struct SkillData {
    last_10: VecDeque<DamageEntry>,
    last_30: VecDeque<DamageEntry>,
    last_50: VecDeque<DamageEntry>,
}

#[derive(Debug, Clone, Default)]
struct DamageAnalyzerData {
    top_10_skills: Vec<(String, u32)>,
    highest_normal_attack: Option<(u32, u64)>,
    skill_averages: HashMap<String, SkillData>,
    last_5_min_top_10: Vec<(String, u32)>,
    last_10_min_top_10: Vec<(String, u32)>,
    last_60_min_top_10: Vec<(String, u32)>,
    last_24_hours_top_10: Vec<(String, u32)>,
    top_damage_by_target: HashMap<String, Vec<(String, u32)>>,
}

// New data structures for the experience analyzer plugin
#[derive(Debug, Clone, Default)]
struct ExpEntry {
    exp: u32,
    timestamp: u64,
}

#[derive(Debug, Clone, Default)]
struct ExpAnalyzerData {
    exp_gains: VecDeque<ExpEntry>,
    exp_special_gains: VecDeque<ExpEntry>,
    exp_mount_gains: VecDeque<ExpEntry>,
    exp_mastery_gains: VecDeque<ExpEntry>,
}

// Settings struct to hold user preferences.
#[derive(Serialize, Deserialize, Clone, Debug)]
struct Settings {
    selected_pid: Option<u32>,
    scan_interval_ms: u64,
    timestamp_format: TimestampFormat,
    channel_colors: HashMap<ChatChannel, [u8; 4]>, // RGBA
    channel_audio: HashMap<ChatChannel, bool>,
    channel_audio_file: HashMap<ChatChannel, PathBuf>,
    subchannel_audio: HashMap<String, bool>,
    subchannel_audio_file: HashMap<String, PathBuf>,
    hide_subchannel_messages: bool,
    log_file_size_limit_mb: u64,
    channel_groups: Vec<ChannelGroup>,
    show_debug_messages: bool,
    show_icons: bool,
    shorten_combat_numbers: bool,
    enable_damage_analyzer: bool,
    enable_exp_analyzer: bool,
    font_size: f32,
    font_name: String,
    hide_subchannel_from_parent_all: HashMap<ChatChannel, bool>,
}

impl Default for Settings {
    fn default() -> Self {
        let mut default_colors = HashMap::new();
        default_colors.insert(ChatChannel::Say, [0xFF, 0xFF, 0xFF, 0xFF]);
        default_colors.insert(ChatChannel::Whisper, [0x80, 0x00, 0x80, 0xFF]);
        default_colors.insert(ChatChannel::Party, [0x23, 0xFB, 0xEE, 0xFF]);
        default_colors.insert(ChatChannel::Guild, [0x00, 0xfe, 0x00, 0xFF]);
        default_colors.insert(ChatChannel::Yell, [0x00, 0x9C, 0xFF, 0xFF]);
        default_colors.insert(ChatChannel::World, [0xFF, 0xAE, 0x00, 0xFF]);
        default_colors.insert(ChatChannel::Trade, [0xf2, 0xe9, 0xad, 0xFF]);
        default_colors.insert(ChatChannel::Combat, [0xFF, 0xFF, 0xFF, 0xFF]);
        default_colors.insert(ChatChannel::Other, [0xFF, 0xFF, 0xFF, 0xFF]);
        default_colors.insert(ChatChannel::Items, [0xa5, 0xdc, 0xf0, 0xFF]);
        default_colors.insert(ChatChannel::Broadcast, [0xFF, 0x78, 0x37, 0xFF]);
        default_colors.insert(ChatChannel::Announce, [0xFF, 0xFF, 0x00, 0xFF]);
        default_colors.insert(ChatChannel::System, [0xdd, 0x00, 0x00, 0xFF]);
        
        Self {
            selected_pid: None,
            scan_interval_ms: 1000, // 1 second
            timestamp_format: TimestampFormat::OnlyTime,
            channel_colors: default_colors,
            channel_audio: HashMap::new(),
            channel_audio_file: HashMap::new(),
            subchannel_audio: HashMap::new(),
            subchannel_audio_file: HashMap::new(),
            hide_subchannel_messages: false,
            log_file_size_limit_mb: 5,
            channel_groups: Vec::new(),
            show_debug_messages: false,
            show_icons: true,
            shorten_combat_numbers: true,
            enable_damage_analyzer: true, // Changed to true by default
            enable_exp_analyzer: false,
            font_size: 14.0,
            font_name: "monospace".to_string(),
            hide_subchannel_from_parent_all: HashMap::new(),
        }
    }
}

// Function to save settings to a JSON file.
fn save_settings(settings: &Settings) {
    let path = PathBuf::from(SETTINGS_FILE);
    if let Ok(json) = serde_json::to_string_pretty(settings) {
        if let Err(e) = fs::write(&path, json) {
            eprintln!("Failed to save settings to {}: {}", path.display(), e);
        }
    } else {
        eprintln!("Failed to serialize settings.");
    }
}

// Function to load settings from a JSON file.
fn load_settings() -> Settings {
    let path = PathBuf::from(SETTINGS_FILE);
    match fs::read_to_string(&path) {
        Ok(json) => {
            match serde_json::from_str(&json) {
                Ok(settings) => {
                    println!("Settings loaded successfully from {}", path.display());
                    settings
                }
                Err(e) => {
                    eprintln!("Failed to deserialize settings: {}. Using default.", e);
                    Settings::default()
                }
            }
        }
        Err(e) => {
            println!("Settings file not found or could not be read: {}. Using default.", e);
            Settings::default()
        }
    }
}

// Helper to play a sound from a file path or a default ding.
fn play_sound_from_file(sink: &Sink, path: Option<&Path>) {
    if let Some(p) = path {
        if let Ok(file) = std::fs::File::open(p) {
            let buffer = std::io::BufReader::new(file);
            if let Ok(source) = Decoder::new(buffer) {
                sink.append(source);
                return;
            } else {
                eprintln!("Failed to decode audio file: {:?}. Is the file format supported (WAV, MP3, FLAC)?", p);
            }
        } else {
            eprintln!("Failed to open audio file: {:?}. Does the file exist at this path and do you have read permissions?", p);
        }
    }
    // Fallback to default ding sound
    let source = SineWave::new(1000.0).take_duration(Duration::from_millis(100));
    sink.append(source);
}

// The main application struct for our GUI
struct ChatLoggerApp {
    messages: Vec<ChatMessage>,
    receiver: mpsc::Receiver<ChatMessage>,
    selected_channel: String,
    selected_sub_channel: String,
    
    // Settings
    settings: Settings,
    temp_settings: Settings, // A temporary copy for editing in the options window
    settings_sender: mpsc::Sender<Settings>,
    show_settings_window: bool,
    show_channel_group_editor: bool,
    show_damage_analyzer_window: bool,
    show_exp_analyzer_window: bool,
    editing_group_index: Option<usize>,
    is_first_scan_done: bool,
    selected_target: String,

    // PID selection
    available_pids: Vec<(Pid, String)>,
    selected_pid_index: usize,

    // Audio
    _stream: OutputStream,
    audio_sink: Sink,
    file_dialog_request_tx: mpsc::Sender<(ChatChannel, String)>,
    file_dialog_response_rx: mpsc::Receiver<(ChatChannel, String, Option<PathBuf>)>,

    // Status bar metrics
    avg_scan_time: f64,
    scan_time_history: Vec<Duration>,

    // Damage Analyzer data
    damage_data: DamageAnalyzerData,

    // Experience Analyzer data
    exp_data: ExpAnalyzerData,
}

impl ChatLoggerApp {
    fn new(
        receiver: mpsc::Receiver<ChatMessage>,
        settings_sender: mpsc::Sender<Settings>,
        available_pids: Vec<(Pid, String)>,
        settings: Settings,
        stream: OutputStream,
        sink: Sink,
        file_dialog_request_tx: mpsc::Sender<(ChatChannel, String)>,
        file_dialog_response_rx: mpsc::Receiver<(ChatChannel, String, Option<PathBuf>)>,
    ) -> Self {
        let selected_pid_index = settings.selected_pid.and_then(|pid| {
            available_pids.iter().position(|(p, _)| p.as_u32() == pid)
        }).unwrap_or(0);

        Self {
            messages: Vec::new(),
            receiver,
            selected_channel: "All".to_string(),
            selected_sub_channel: "All".to_string(),
            selected_target: "All".to_string(),
            settings: settings.clone(),
            temp_settings: settings,
            settings_sender,
            show_settings_window: false,
            show_channel_group_editor: false,
            show_damage_analyzer_window: false,
            show_exp_analyzer_window: false,
            editing_group_index: None,
            is_first_scan_done: false,
            available_pids,
            selected_pid_index,
            _stream: stream,
            audio_sink: sink,
            file_dialog_request_tx,
            file_dialog_response_rx,
            avg_scan_time: 0.0,
            scan_time_history: Vec::with_capacity(100),
            damage_data: DamageAnalyzerData::default(),
            exp_data: ExpAnalyzerData::default(),
        }
    }

    fn draw_settings_window(&mut self, ctx: &eframe::egui::Context) {
        let mut close_window = false;
        
        Window::new("Settings")
            .id(Id::new("settings_window"))
            .open(&mut self.show_settings_window)
            .collapsible(false)
            .resizable(true)
            .show(ctx, |ui| {
                ui.label("General Settings");
                ui.separator();

                // PID selection
                if self.available_pids.len() > 1 {
                    ui.horizontal(|ui| {
                        ui.label("Select Process:");
                        ComboBox::from_id_source("pid_selector")
                            .selected_text(format!("{} - {}", 
                                self.available_pids[self.selected_pid_index].1,
                                self.available_pids[self.selected_pid_index].0,
                            ))
                            .show_ui(ui, |ui| {
                                for (i, (pid, name)) in self.available_pids.iter().enumerate() {
                                    if ui.selectable_label(self.selected_pid_index == i, format!("{} - {}", name, pid)).clicked() {
                                        self.temp_settings.selected_pid = Some(pid.as_u32());
                                    }
                                }
                            });
                    });
                } else {
                    ui.label(format!("Scanning process: {}", PROCESS_NAME));
                }

                // Scan interval
                ui.horizontal(|ui| {
                    ui.label("Scanning Interval (ms):");
                    ui.add(Slider::new(&mut self.temp_settings.scan_interval_ms, 100..=5000));
                });
                ui.separator();
                
                // Log file size limit
                ui.horizontal(|ui| {
                    ui.label("Log file size limit (MB):");
                    ui.add(Slider::new(&mut self.temp_settings.log_file_size_limit_mb, 1..=500));
                });
                ui.separator();

                // Timestamp format
                ui.label("Timestamp Format:");
                ComboBox::from_id_source("timestamp_format")
                    .selected_text(self.temp_settings.timestamp_format.to_string())
                    .show_ui(ui, |ui| {
                        if ui.selectable_label(self.temp_settings.timestamp_format == TimestampFormat::Full, TimestampFormat::Full.to_string()).clicked() {
                            self.temp_settings.timestamp_format = TimestampFormat::Full;
                        }
                        if ui.selectable_label(self.temp_settings.timestamp_format == TimestampFormat::OnlyTime, TimestampFormat::OnlyTime.to_string()).clicked() {
                            self.temp_settings.timestamp_format = TimestampFormat::OnlyTime;
                        }
                        if ui.selectable_label(self.temp_settings.timestamp_format == TimestampFormat::Short, TimestampFormat::Short.to_string()).clicked() {
                            self.temp_settings.timestamp_format = TimestampFormat::Short;
                        }
                        if ui.selectable_label(self.temp_settings.timestamp_format == TimestampFormat::None, TimestampFormat::None.to_string()).clicked() {
                            self.temp_settings.timestamp_format = TimestampFormat::None;
                        }
                    });
                ui.separator();

                // Font settings
                ui.horizontal(|ui| {
                    ui.label("Font Size:");
                    ui.add(Slider::new(&mut self.temp_settings.font_size, 8.0..=24.0));
                });
                ui.separator();

                // Debug messages
                ui.checkbox(&mut self.temp_settings.show_debug_messages, "Show Debug messages");
                ui.checkbox(&mut self.temp_settings.show_icons, "Show Icons");
                ui.checkbox(&mut self.temp_settings.shorten_combat_numbers, "Shorten Combat Numbers (e.g. 100k)");
                ui.checkbox(&mut self.temp_settings.enable_damage_analyzer, "Enable Damage Analyzer");
                ui.checkbox(&mut self.temp_settings.enable_exp_analyzer, "Enable Experience Analyzer");
                ui.separator();

                // Channel Colors and Audio
                ScrollArea::vertical().show(ui, |ui| {
                    ui.heading("Channel Settings");
                    for channel in ChatChannel::all().iter().filter(|c| **c != ChatChannel::All) {
                        ui.collapsing(channel.to_string(), |ui| {
                            let color_rgba = self.temp_settings.channel_colors.get(channel).cloned().unwrap_or([0, 0, 0, 0]);
                            let mut color_egui = egui::Color32::from_rgba_unmultiplied(color_rgba[0], color_rgba[1], color_rgba[2], color_rgba[3]);
                            
                            let mut audio_enabled = *self.temp_settings.channel_audio.get(channel).unwrap_or(&false);

                            ui.horizontal(|ui| {
                                ui.label("Color:");
                                ui.color_edit_button_srgba(&mut color_egui);
                                
                                ui.label("Play Sound:");
                                ui.checkbox(&mut audio_enabled, "");
                            });

                            ui.horizontal(|ui| {
                                if ui.button("Select Audio File...").clicked() {
                                    if let Err(e) = self.file_dialog_request_tx.send((*channel, String::new())) {
                                        eprintln!("Failed to send file dialog request: {}", e);
                                    }
                                }
                                if let Some(path) = self.temp_settings.channel_audio_file.get(channel) {
                                    ui.label(path.display().to_string());
                                }
                            });
                            
                            self.temp_settings.channel_colors.insert(*channel, color_egui.to_array());
                            self.temp_settings.channel_audio.insert(*channel, audio_enabled);

                            // Sub-channels
                            if let Some(sub_channels) = SUB_CHANNELS.get(channel) {
                                ui.separator();
                                ui.label("Sub-channel Settings:");
                                for sub_channel in sub_channels {
                                    ui.horizontal(|ui| {
                                        let mut sub_audio_enabled = *self.temp_settings.subchannel_audio.get(sub_channel.name).unwrap_or(&false);
                                        ui.label(sub_channel.name);
                                        ui.checkbox(&mut sub_audio_enabled, "Play Sound");
                                        self.temp_settings.subchannel_audio.insert(sub_channel.name.to_string(), sub_audio_enabled);
                                    });
                                    ui.horizontal(|ui| {
                                        if ui.button("Select Audio File...").clicked() {
                                            if let Err(e) = self.file_dialog_request_tx.send((*channel, sub_channel.name.to_string())) {
                                                eprintln!("Failed to send file dialog request: {}", e);
                                            }
                                        }
                                        if let Some(path) = self.temp_settings.subchannel_audio_file.get(sub_channel.name) {
                                            ui.label(path.display().to_string());
                                        }
                                    });
                                }
                            }
                        });
                    }
                });
                
                ui.separator();

                ui.checkbox(&mut self.temp_settings.hide_subchannel_messages, "Hide sub-channel messages from main tab");
                
                ui.label("Channel Groups");
                ui.horizontal(|ui| {
                    if ui.button("Add New Group").clicked() {
                        self.temp_settings.channel_groups.push(ChannelGroup {
                            name: "New Group".to_string(),
                            channels: HashSet::new(),
                            excluded_subchannels: HashSet::new(),
                        });
                        self.editing_group_index = Some(self.temp_settings.channel_groups.len() - 1);
                        self.show_channel_group_editor = true;
                    }
                });

                ui.separator();
                ui.horizontal(|ui| {
                    if ui.button("Save").clicked() {
                        self.settings = self.temp_settings.clone();
                        save_settings(&self.settings);
                        if let Err(e) = self.settings_sender.send(self.settings.clone()) {
                            eprintln!("Failed to send settings to scanner thread: {}", e);
                        }
                        close_window = true;
                    }
                    if ui.button("Cancel").clicked() {
                        self.temp_settings = self.settings.clone();
                        close_window = true;
                    }
                });
            });

        if close_window {
            self.show_settings_window = false;
        }
    }

    fn draw_channel_group_editor(&mut self, ctx: &egui::Context) {
        let mut close_window = false;
        
        Window::new("Edit Channel Group")
            .id(Id::new("channel_group_editor"))
            .open(&mut self.show_channel_group_editor)
            .collapsible(false)
            .resizable(false)
            .show(ctx, |ui| {
                if let Some(index) = self.editing_group_index {
                    // Check if the index is valid before proceeding
                    if let Some(group) = self.temp_settings.channel_groups.get_mut(index) {
                        ui.label("Group Name:");
                        ui.add(TextEdit::singleline(&mut group.name).desired_width(ui.available_width()));
                        ui.separator();

                        ui.label("Channels to Include:");
                        for channel in ChatChannel::all().iter().filter(|c| **c != ChatChannel::All) {
                            let mut is_checked = group.channels.contains(channel);
                            ui.checkbox(&mut is_checked, channel.to_string());
                            if is_checked {
                                group.channels.insert(*channel);
                            } else {
                                group.channels.remove(channel);
                            }
                        }

                        ui.separator();
                        ui.label("Sub-channels to Exclude:");
                        for channel in group.channels.iter().filter(|c| SUB_CHANNELS.contains_key(c)) {
                            ui.collapsing(channel.to_string(), |ui| {
                                if let Some(sub_channels) = SUB_CHANNELS.get(channel) {
                                    for sub_channel in sub_channels {
                                        let mut is_checked = group.excluded_subchannels.contains(sub_channel.name);
                                        ui.checkbox(&mut is_checked, sub_channel.name);
                                        if is_checked {
                                            group.excluded_subchannels.insert(sub_channel.name.to_string());
                                        } else {
                                            group.excluded_subchannels.remove(sub_channel.name);
                                        }
                                    }
                                }
                            });
                        }

                        ui.separator();
                        ui.horizontal(|ui| {
                            if ui.button("Save Group").clicked() {
                                close_window = true;
                            }
                            if ui.button("Delete Group").clicked() {
                                self.temp_settings.channel_groups.remove(index);
                                close_window = true;
                            }
                            if ui.button("Cancel").clicked() {
                                close_window = true;
                            }
                        });
                    } else {
                        // The group was not found (e.g., already deleted), so close the window
                        close_window = true;
                    }
                }
            });

        if close_window {
            self.show_channel_group_editor = false;
            // Reset the selected channel if the deleted group was selected
            if let Some(index) = self.editing_group_index {
                if index < self.settings.channel_groups.len() && self.selected_channel == self.settings.channel_groups[index].name {
                    self.selected_channel = "All".to_string();
                }
            }
            self.editing_group_index = None;
        }
    }

    fn draw_damage_analyzer_window(&mut self, ctx: &egui::Context) {
        Window::new("Damage Analyzer")
            .id(Id::new("damage_analyzer_window"))
            .open(&mut self.show_damage_analyzer_window)
            .collapsible(false)
            .resizable(true)
            .show(ctx, |ui| {
                ui.collapsing("Highest Damage (All Time)", |ui| {
                    ui.horizontal(|ui| {
                        ui.vertical(|ui| {
                            ui.label(RichText::new("Top 10 Skills:").strong());
                            for (_i, (skill, damage)) in self.damage_data.top_10_skills.iter().enumerate() {
                                ui.label(format!("{}: {}", skill, format_number(*damage)));
                            }
                        });
                        ui.add_space(ui.available_width() * 0.5);
                        ui.vertical(|ui| {
                            ui.label(RichText::new("Highest Normal Attack:").strong());
                            if let Some((damage, _)) = self.damage_data.highest_normal_attack {
                                ui.label(format!("{}", format_number(damage)));
                            }
                        });
                    });
                });

                ui.collapsing("Highest Damage by Time Period", |ui| {
                    ui.columns(4, |columns| {
                        columns[0].label(RichText::new("Last 5 Minutes").strong());
                        for (_i, (skill, damage)) in self.damage_data.last_5_min_top_10.iter().enumerate() {
                            columns[0].label(format!("{}: {}", skill, format_number(*damage)));
                        }
                        columns[1].label(RichText::new("Last 10 Minutes").strong());
                        for (_i, (skill, damage)) in self.damage_data.last_10_min_top_10.iter().enumerate() {
                            columns[1].label(format!("{}: {}", skill, format_number(*damage)));
                        }
                        columns[2].label(RichText::new("Last 60 Minutes").strong());
                        for (_i, (skill, damage)) in self.damage_data.last_60_min_top_10.iter().enumerate() {
                            columns[2].label(format!("{}: {}", skill, format_number(*damage)));
                        }
                        columns[3].label(RichText::new("Last 24 Hours").strong());
                        for (_i, (skill, damage)) in self.damage_data.last_24_hours_top_10.iter().enumerate() {
                            columns[3].label(format!("{}: {}", skill, format_number(*damage)));
                        }
                    });
                });
                
                ui.collapsing("Average Damage per Skill", |ui| {
                    ScrollArea::vertical().show(ui, |ui| {
                        let mut sorted_averages: Vec<(&String, f64)> = self.damage_data.skill_averages.iter().map(|(skill_name, skill_data)| {
                            let avg = if !skill_data.last_50.is_empty() {
                                skill_data.last_50.iter().map(|e| e.damage as f64).sum::<f64>() / skill_data.last_50.len() as f64
                            } else { 0.0 };
                            (skill_name, avg)
                        }).collect();
                        sorted_averages.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap_or(std::cmp::Ordering::Equal));

                        ui.columns(4, |columns| {
                            columns[0].label(RichText::new("Skill").strong());
                            columns[1].label(RichText::new("Avg (10)").strong());
                            columns[2].label(RichText::new("Avg (30)").strong());
                            columns[3].label(RichText::new("Avg (50)").strong());
                        });
                        ui.separator();

                        for (skill_name, _) in &sorted_averages {
                            let skill_data = self.damage_data.skill_averages.get(*skill_name).unwrap();

                            let avg_10 = if !skill_data.last_10.is_empty() {
                                skill_data.last_10.iter().map(|e| e.damage as f64).sum::<f64>() / skill_data.last_10.len() as f64
                            } else { 0.0 };
                            let avg_30 = if !skill_data.last_30.is_empty() {
                                skill_data.last_30.iter().map(|e| e.damage as f64).sum::<f64>() / skill_data.last_30.len() as f64
                            } else { 0.0 };
                            let avg_50 = if !skill_data.last_50.is_empty() {
                                skill_data.last_50.iter().map(|e| e.damage as f64).sum::<f64>() / skill_data.last_50.len() as f64
                            } else { 0.0 };
                            
                            ui.columns(4, |columns| {
                                columns[0].label(*skill_name);
                                columns[1].label(format!("{:.2}", avg_10));
                                columns[2].label(format!("{:.2}", avg_30));
                                columns[3].label(format!("{:.2}", avg_50));
                            });
                        }
                    });
                });
                
                ui.collapsing("Highest Damage by Target", |ui| {
                    let mut targets: Vec<String> = self.damage_data.top_damage_by_target.keys().cloned().collect();
                    targets.sort();
                    if targets.is_empty() {
                        ui.label("No target data available.");
                    } else {
                        let mut selected_target_name = self.selected_target.clone();
                        if !targets.contains(&selected_target_name) {
                            selected_target_name = targets.first().unwrap().clone();
                        }
                        
                        ui.horizontal(|ui| {
                            ui.label("Select Target:");
                            egui::ComboBox::from_id_source("target_selector")
                                .selected_text(&selected_target_name)
                                .show_ui(ui, |ui| {
                                    for target in &targets {
                                        if ui.selectable_label(selected_target_name == *target, target).clicked() {
                                            selected_target_name = target.clone();
                                        }
                                    }
                                });
                        });
                        self.selected_target = selected_target_name;

                        ui.separator();
                        
                        if let Some(top_skills) = self.damage_data.top_damage_by_target.get(&self.selected_target) {
                            ui.label(RichText::new(format!("Top 10 Skills against {}:", self.selected_target)).strong());
                            for (_i, (skill, damage)) in top_skills.iter().enumerate() {
                                ui.label(format!("{}: {}", skill, format_number(*damage)));
                            }
                        }
                    }
                });

                ui.add_space(10.0);
            });
    }

    fn draw_exp_analyzer_window(&mut self, ctx: &egui::Context) {
        Window::new("Experience Analyzer")
            .id(Id::new("exp_analyzer_window"))
            .open(&mut self.show_exp_analyzer_window)
            .collapsible(false)
            .resizable(true)
            .show(ctx, |ui| {
                ui.heading("Average Experience Gains");
                ui.separator();
                
                let now = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_secs();

                // Normal EXP
                let last_5_min_exp: Vec<&ExpEntry> = self.exp_data.exp_gains.iter().filter(|e| e.timestamp >= now.saturating_sub(300)).collect();
                let last_10_min_exp: Vec<&ExpEntry> = self.exp_data.exp_gains.iter().filter(|e| e.timestamp >= now.saturating_sub(600)).collect();
                let last_60_min_exp: Vec<&ExpEntry> = self.exp_data.exp_gains.iter().filter(|e| e.timestamp >= now.saturating_sub(3600)).collect();
                
                let total_exp_5m: u32 = last_5_min_exp.iter().map(|e| e.exp).sum();
                let total_exp_10m: u32 = last_10_min_exp.iter().map(|e| e.exp).sum();
                let total_exp_60m: u32 = last_60_min_exp.iter().map(|e| e.exp).sum();

                // Special EXP
                let last_5_min_special: Vec<&ExpEntry> = self.exp_data.exp_special_gains.iter().filter(|e| e.timestamp >= now.saturating_sub(300)).collect();
                let last_10_min_special: Vec<&ExpEntry> = self.exp_data.exp_special_gains.iter().filter(|e| e.timestamp >= now.saturating_sub(600)).collect();
                let last_60_min_special: Vec<&ExpEntry> = self.exp_data.exp_special_gains.iter().filter(|e| e.timestamp >= now.saturating_sub(3600)).collect();
                
                let total_special_5m: u32 = last_5_min_special.iter().map(|e| e.exp).sum();
                let total_special_10m: u32 = last_10_min_special.iter().map(|e| e.exp).sum();
                let total_special_60m: u32 = last_60_min_special.iter().map(|e| e.exp).sum();

                // Mount EXP
                let last_5_min_mount: Vec<&ExpEntry> = self.exp_data.exp_mount_gains.iter().filter(|e| e.timestamp >= now.saturating_sub(300)).collect();
                let last_10_min_mount: Vec<&ExpEntry> = self.exp_data.exp_mount_gains.iter().filter(|e| e.timestamp >= now.saturating_sub(600)).collect();
                let last_60_min_mount: Vec<&ExpEntry> = self.exp_data.exp_mount_gains.iter().filter(|e| e.timestamp >= now.saturating_sub(3600)).collect();
                
                let total_mount_5m: u32 = last_5_min_mount.iter().map(|e| e.exp).sum();
                let total_mount_10m: u32 = last_10_min_mount.iter().map(|e| e.exp).sum();
                let total_mount_60m: u32 = last_60_min_mount.iter().map(|e| e.exp).sum();
                
                // Mastery EXP
                let last_5_min_mastery: Vec<&ExpEntry> = self.exp_data.exp_mastery_gains.iter().filter(|e| e.timestamp >= now.saturating_sub(300)).collect();
                let last_10_min_mastery: Vec<&ExpEntry> = self.exp_data.exp_mastery_gains.iter().filter(|e| e.timestamp >= now.saturating_sub(600)).collect();
                let last_60_min_mastery: Vec<&ExpEntry> = self.exp_data.exp_mastery_gains.iter().filter(|e| e.timestamp >= now.saturating_sub(3600)).collect();
                
                let total_mastery_5m: u32 = last_5_min_mastery.iter().map(|e| e.exp).sum();
                let total_mastery_10m: u32 = last_10_min_mastery.iter().map(|e| e.exp).sum();
                let total_mastery_60m: u32 = last_60_min_mastery.iter().map(|e| e.exp).sum();

                // Table for Normal and Special EXP
                ui.label(RichText::new("Normal & Special EXP").strong());
                ui.columns(4, |columns| {
                    columns[0].label(RichText::new("Category").strong());
                    columns[1].label(RichText::new("Last 5m").strong());
                    columns[2].label(RichText::new("Last 10m").strong());
                    columns[3].label(RichText::new("Last 60m").strong());
                });
                ui.separator();
                
                ui.columns(4, |columns| {
                    columns[0].label("Normal EXP (Total)");
                    columns[1].label(format_number(total_exp_5m));
                    columns[2].label(format_number(total_exp_10m));
                    columns[3].label(format_number(total_exp_60m));
                });
                ui.columns(4, |columns| {
                    columns[0].label("Normal EXP (Avg)");
                    columns[1].label(format!("{:.2}", if !last_5_min_exp.is_empty() { total_exp_5m as f64 / last_5_min_exp.len() as f64 } else { 0.0 }));
                    columns[2].label(format!("{:.2}", if !last_10_min_exp.is_empty() { total_exp_10m as f64 / last_10_min_exp.len() as f64 } else { 0.0 }));
                    columns[3].label(format!("{:.2}", if !last_60_min_exp.is_empty() { total_exp_60m as f64 / last_60_min_exp.len() as f64 } else { 0.0 }));
                });

                ui.columns(4, |columns| {
                    columns[0].label("Special EXP (Total)");
                    columns[1].label(format_number(total_special_5m));
                    columns[2].label(format_number(total_special_10m));
                    columns[3].label(format_number(total_special_60m));
                });
                ui.columns(4, |columns| {
                    columns[0].label("Special EXP (Avg)");
                    columns[1].label(format!("{:.2}", if !last_5_min_special.is_empty() { total_special_5m as f64 / last_5_min_special.len() as f64 } else { 0.0 }));
                    columns[2].label(format!("{:.2}", if !last_10_min_special.is_empty() { total_special_10m as f64 / last_10_min_special.len() as f64 } else { 0.0 }));
                    columns[3].label(format!("{:.2}", if !last_60_min_special.is_empty() { total_special_60m as f64 / last_60_min_special.len() as f64 } else { 0.0 }));
                });

                ui.separator();

                // Table for Mount and Mastery EXP
                ui.label(RichText::new("Mount & Mastery EXP").strong());
                ui.columns(4, |columns| {
                    columns[0].label(RichText::new("Category").strong());
                    columns[1].label(RichText::new("Last 5m").strong());
                    columns[2].label(RichText::new("Last 10m").strong());
                    columns[3].label(RichText::new("Last 60m").strong());
                });
                ui.separator();
                
                ui.columns(4, |columns| {
                    columns[0].label("Mount EXP (Total)");
                    columns[1].label(format_number(total_mount_5m));
                    columns[2].label(format_number(total_mount_10m));
                    columns[3].label(format_number(total_mount_60m));
                });
                ui.columns(4, |columns| {
                    columns[0].label("Mount EXP (Avg)");
                    columns[1].label(format!("{:.2}", if !last_5_min_mount.is_empty() { total_mount_5m as f64 / last_5_min_mount.len() as f64 } else { 0.0 }));
                    columns[2].label(format!("{:.2}", if !last_10_min_mount.is_empty() { total_mount_10m as f64 / last_10_min_mount.len() as f64 } else { 0.0 }));
                    columns[3].label(format!("{:.2}", if !last_60_min_mount.is_empty() { total_mount_60m as f64 / last_60_min_mount.len() as f64 } else { 0.0 }));
                });

                ui.columns(4, |columns| {
                    columns[0].label("Mastery EXP (Total)");
                    columns[1].label(format_number(total_mastery_5m));
                    columns[2].label(format_number(total_mastery_10m));
                    columns[3].label(format_number(total_mastery_60m));
                });
                ui.columns(4, |columns| {
                    columns[0].label("Mastery EXP (Avg)");
                    columns[1].label(format!("{:.2}", if !last_5_min_mastery.is_empty() { total_mastery_5m as f64 / last_5_min_mastery.len() as f64 } else { 0.0 }));
                    columns[2].label(format!("{:.2}", if !last_10_min_mastery.is_empty() { total_mastery_10m as f64 / last_10_min_mastery.len() as f64 } else { 0.0 }));
                    columns[3].label(format!("{:.2}", if !last_60_min_mastery.is_empty() { total_mastery_60m as f64 / last_60_min_mastery.len() as f64 } else { 0.0 }));
                });
            });
    }

    fn add_damage_entry(&mut self, skill_name: String, target_name: String, damage: u32) {
        let now = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_secs();
        let entry = DamageEntry { damage, timestamp: now };

        // Update all-time top 10
        let mut found_in_top_10 = false;
        for (_i, (s_name, s_damage)) in self.damage_data.top_10_skills.iter_mut().enumerate() {
            if s_name == &skill_name {
                if damage > *s_damage {
                    *s_damage = damage;
                }
                found_in_top_10 = true;
                break;
            }
        }
        if !found_in_top_10 {
            self.damage_data.top_10_skills.push((skill_name.clone(), damage));
        }
        self.damage_data.top_10_skills.sort_by(|a, b| b.1.cmp(&a.1));
        self.damage_data.top_10_skills.truncate(10);
        
        // Update top damage by target
        let top_skills_for_target = self.damage_data.top_damage_by_target.entry(target_name.clone()).or_insert_with(Vec::new);
        let mut found_for_target = false;
        for (_i, (s_name, s_damage)) in top_skills_for_target.iter_mut().enumerate() {
            if s_name == &skill_name {
                if damage > *s_damage {
                    *s_damage = damage;
                }
                found_for_target = true;
                break;
            }
        }
        if !found_for_target {
            top_skills_for_target.push((skill_name.clone(), damage));
        }
        top_skills_for_target.sort_by(|a, b| b.1.cmp(&a.1));
        top_skills_for_target.truncate(10);


        // Update rolling averages
        let skill_data = self.damage_data.skill_averages.entry(skill_name.clone()).or_insert_with(Default::default);
        skill_data.last_10.push_back(entry.clone());
        if skill_data.last_10.len() > 10 {
            skill_data.last_10.pop_front();
        }
        skill_data.last_30.push_back(entry.clone());
        if skill_data.last_30.len() > 30 {
            skill_data.last_30.pop_front();
        }
        skill_data.last_50.push_back(entry);
        if skill_data.last_50.len() > 50 {
            skill_data.last_50.pop_front();
        }
    }
}

// Helper function to format large numbers
fn format_number(n: u32) -> String {
    if n >= 1_000 {
        format!("{:.1}k", n as f64 / 1_000.0)
    } else {
        n.to_string()
    }
}

impl eframe::App for ChatLoggerApp {
    fn update(&mut self, ctx: &eframe::egui::Context, _frame: &mut eframe::Frame) {
        while let Ok(msg) = self.receiver.try_recv() {
            let message_channel = ChatChannel::from_prefix(&msg.prefix).unwrap_or(ChatChannel::Other);
            
            // Check for damage messages to update analyzer data
            if message_channel == ChatChannel::Combat && self.settings.enable_damage_analyzer {
                if let Some(raw_content) = &msg.raw_content {
                    if let Some(caps) = COMBAT_SKILL_REGEX.captures(raw_content) {
                        let skill_name = caps.get(1).map(|m| m.as_str().to_string()).unwrap_or_default();
                        let target_name = caps.get(2).map(|m| m.as_str().to_string()).unwrap_or_default();
                        let damage_str = caps.get(3).map(|m| m.as_str().to_string()).unwrap_or_default();
                        if let Ok(damage) = damage_str.parse::<u32>() {
                            self.add_damage_entry(skill_name, target_name, damage);
                        }
                    } else if let Some(caps) = COMBAT_NORMAL_REGEX.captures(raw_content) {
                        let damage_str = caps.get(1).map(|m| m.as_str().to_string()).unwrap_or_default();
                        if let Ok(damage) = damage_str.parse::<u32>() {
                            let now = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_secs();
                            if self.damage_data.highest_normal_attack.is_none() || damage > self.damage_data.highest_normal_attack.unwrap().0 {
                                self.damage_data.highest_normal_attack = Some((damage, now));
                            }
                        }
                    }
                }
            }

            // Check for EXP messages to update analyzer data
            if message_channel == ChatChannel::Other && self.settings.enable_exp_analyzer {
                if let Some(caps) = EXP_REGEX.captures(&msg.content) {
                    if let Some(exp_str) = caps.get(1).map(|m| m.as_str()) {
                        if let Ok(exp) = exp_str.parse::<u32>() {
                            let now = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_secs();
                            self.exp_data.exp_gains.push_back(ExpEntry { exp, timestamp: now });
                        }
                    }
                }
                if let Some(caps) = EXP_SPECIAL_REGEX.captures(&msg.content) {
                    if let Some(exp_str) = caps.get(1).map(|m| m.as_str()) {
                        if let Ok(exp) = exp_str.parse::<u32>() {
                            let now = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_secs();
                            self.exp_data.exp_special_gains.push_back(ExpEntry { exp, timestamp: now });
                        }
                    }
                }
            }
            
            // Handle new System EXP subchannels
            if message_channel == ChatChannel::System && self.settings.enable_exp_analyzer {
                if let Some(caps) = MOUNT_EXP_REGEX.captures(&msg.content) {
                    if let Ok(exp) = caps.get(1).unwrap().as_str().parse::<u32>() {
                        let now = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_secs();
                        self.exp_data.exp_mount_gains.push_back(ExpEntry { exp, timestamp: now });
                    }
                } else if let Some(caps) = MASTERY_EXP_REGEX.captures(&msg.content) {
                    if let Ok(exp) = caps.get(1).unwrap().as_str().parse::<u32>() {
                        let now = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_secs();
                        self.exp_data.exp_mastery_gains.push_back(ExpEntry { exp, timestamp: now });
                    }
                }
            }

            if msg.prefix == "Status" {
                if let Some(caps) = DURATION_REGEX.captures(&msg.content) {
                    if let Some(duration_str) = caps.get(1) {
                        if let Ok(duration_ms) = duration_str.as_str().parse::<f64>() {
                            let duration = Duration::from_micros((duration_ms * 1000.0) as u64);
                            self.scan_time_history.push(duration);
                            if self.scan_time_history.len() > 100 {
                                self.scan_time_history.remove(0);
                            }
                            self.avg_scan_time = self.scan_time_history.iter().map(|d| d.as_micros() as f64).sum::<f64>() / self.scan_time_history.len() as f64 / 1000.0;
                        }
                    }
                }
                self.is_first_scan_done = true;
            } else if msg.do_ding && self.is_first_scan_done {
                let audio_file_path = if let Some(sub_channel_name) = &msg.sub_channel {
                    self.settings.subchannel_audio_file.get(sub_channel_name)
                } else {
                    ChatChannel::from_prefix(&msg.prefix)
                        .and_then(|c| self.settings.channel_audio_file.get(&c))
                };
                play_sound_from_file(&self.audio_sink, audio_file_path.map(|p| p.as_path()));
            }
            self.messages.push(msg);
        }

        // Check for results from the file dialog thread
        while let Ok((channel_type, subchannel_name, path)) = self.file_dialog_response_rx.try_recv() {
            if !subchannel_name.is_empty() {
                if let Some(p) = path {
                    self.settings.subchannel_audio_file.insert(subchannel_name.clone(), p);
                } else {
                    self.settings.subchannel_audio_file.remove(&subchannel_name);
                }
            } else {
                if let Some(p) = path {
                    self.settings.channel_audio_file.insert(channel_type, p);
                } else {
                    self.settings.channel_audio_file.remove(&channel_type);
                }
            }

            // After a file dialog response, we save the updated settings and send them to the scanner thread.
            save_settings(&self.settings);
            if let Err(e) = self.settings_sender.send(self.settings.clone()) {
                eprintln!("Failed to send updated settings to scanner thread: {}", e);
            }
            
            self.temp_settings = self.settings.clone();
        }
        
        // Update font size
        let mut style = (*ctx.style()).clone();
        style.text_styles.get_mut(&TextStyle::Body).unwrap().size = self.settings.font_size;
        ctx.set_style(style);

        ctx.request_repaint();

        // Update time-based damage data
        let now_secs = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_secs();
        let min_5 = now_secs.saturating_sub(300);
        let min_10 = now_secs.saturating_sub(600);
        let min_60 = now_secs.saturating_sub(3600);
        let min_24h = now_secs.saturating_sub(86400);

        let mut all_damage_entries: Vec<(String, &DamageEntry)> = Vec::new();
        for (skill_name, skill_data) in &self.damage_data.skill_averages {
            for entry in &skill_data.last_50 {
                all_damage_entries.push((skill_name.clone(), entry));
            }
        }
        
        // Update last 5 min top 10
        let mut last_5_min_top_10_map: HashMap<String, u32> = HashMap::new();
        for (skill_name, entry) in &all_damage_entries {
            if entry.timestamp >= min_5 {
                let current_max = last_5_min_top_10_map.entry(skill_name.clone()).or_insert(0);
                if entry.damage > *current_max {
                    *current_max = entry.damage;
                }
            }
        }
        self.damage_data.last_5_min_top_10 = last_5_min_top_10_map.into_iter().collect();
        self.damage_data.last_5_min_top_10.sort_by(|a, b| b.1.cmp(&a.1));
        self.damage_data.last_5_min_top_10.truncate(10);

        // Update last 10 min top 10
        let mut last_10_min_top_10_map: HashMap<String, u32> = HashMap::new();
        for (skill_name, entry) in &all_damage_entries {
            if entry.timestamp >= min_10 {
                let current_max = last_10_min_top_10_map.entry(skill_name.clone()).or_insert(0);
                if entry.damage > *current_max {
                    *current_max = entry.damage;
                }
            }
        }
        self.damage_data.last_10_min_top_10 = last_10_min_top_10_map.into_iter().collect();
        self.damage_data.last_10_min_top_10.sort_by(|a, b| b.1.cmp(&a.1));
        self.damage_data.last_10_min_top_10.truncate(10);
        
        // Update last 60 min top 10
        let mut last_60_min_top_10_map: HashMap<String, u32> = HashMap::new();
        for (skill_name, entry) in &all_damage_entries {
            if entry.timestamp >= min_60 {
                let current_max = last_60_min_top_10_map.entry(skill_name.clone()).or_insert(0);
                if entry.damage > *current_max {
                    *current_max = entry.damage;
                }
            }
        }
        self.damage_data.last_60_min_top_10 = last_60_min_top_10_map.into_iter().collect();
        self.damage_data.last_60_min_top_10.sort_by(|a, b| b.1.cmp(&a.1));
        self.damage_data.last_60_min_top_10.truncate(10);

        // Update last 24 hours top 10
        let mut last_24_hours_top_10_map: HashMap<String, u32> = HashMap::new();
        for (skill_name, entry) in &all_damage_entries {
            if entry.timestamp >= min_24h {
                let current_max = last_24_hours_top_10_map.entry(skill_name.clone()).or_insert(0);
                if entry.damage > *current_max {
                    *current_max = entry.damage;
                }
            }
        }
        self.damage_data.last_24_hours_top_10 = last_24_hours_top_10_map.into_iter().collect();
        self.damage_data.last_24_hours_top_10.sort_by(|a, b| b.1.cmp(&a.1));
        self.damage_data.last_24_hours_top_10.truncate(10);
        
        
        eframe::egui::CentralPanel::default().show(ctx, |ui| {
            ui.horizontal(|ui| {
                // Damage Analyzer button
                if self.settings.enable_damage_analyzer {
                    if ui.selectable_label(self.show_damage_analyzer_window, RichText::new("Damage Analyzer").color(Color32::from_rgb(255, 165, 0))).clicked() {
                        self.show_damage_analyzer_window = !self.show_damage_analyzer_window;
                    }
                }
                
                // Experience Analyzer button
                if self.settings.enable_exp_analyzer {
                    if ui.selectable_label(self.show_exp_analyzer_window, RichText::new("Experience Analyzer").color(Color32::from_rgb(255, 165, 0))).clicked() {
                        self.show_exp_analyzer_window = !self.show_exp_analyzer_window;
                    }
                }

                // Main and custom channels
                egui::ScrollArea::horizontal().show(ui, |ui| {
                    if !self.settings.channel_groups.is_empty() {
                        for (_i, group) in self.settings.channel_groups.iter().enumerate() {
                            let button = ui.selectable_label(self.selected_channel == group.name, &group.name);
                            if button.clicked() {
                                self.selected_channel = group.name.clone();
                                self.selected_sub_channel = "All".to_string();
                            }
                            if button.secondary_clicked() {
                                self.editing_group_index = Some(_i);
                                self.show_channel_group_editor = true;
                            }
                        }
                        ui.separator();
                    }
                    
                    for channel in ChatChannel::all() {
                        let text = if self.selected_channel == channel.to_string() {
                            egui::RichText::new(channel.to_string()).strong()
                        } else {
                            egui::RichText::new(channel.to_string())
                        };
                        
                        let button = ui.selectable_label(self.selected_channel == channel.to_string(), text);
                        if button.clicked() {
                            self.selected_channel = channel.to_string();
                            self.selected_sub_channel = "All".to_string();
                        }
                    }
                });

                // Settings button on the right
                ui.with_layout(Layout::right_to_left(Align::Center), |ui| {
                    if ui.button("Settings").clicked() {
                        self.show_settings_window = true;
                    }
                });
            });

            ui.separator();

            // Check if the selected channel has sub-channels and draw a secondary tab bar
            if let Some(parent_channel) = ChatChannel::all().into_iter().find(|c| c.to_string() == self.selected_channel) {
                if let Some(sub_channels) = SUB_CHANNELS.get(&parent_channel) {
                    ui.horizontal(|ui| {
                        // "All" sub-tab
                        let all_sub_tab_text = if self.selected_sub_channel == "All" {
                            egui::RichText::new("All").strong()
                        } else {
                            egui::RichText::new("All")
                        };
                        if ui.selectable_label(self.selected_sub_channel == "All", all_sub_tab_text).clicked() {
                            self.selected_sub_channel = "All".to_string();
                        }

                        // Individual sub-channel tabs
                        for sub_channel in sub_channels {
                            let text = if self.selected_sub_channel == sub_channel.name {
                                egui::RichText::new(sub_channel.name).strong()
                            } else {
                                egui::RichText::new(sub_channel.name)
                            };

                            if ui.selectable_label(self.selected_sub_channel == sub_channel.name, text).clicked() {
                                self.selected_sub_channel = sub_channel.name.to_string();
                            }
                        }

                        // Checkbox to hide sub-channel messages from the parent's "All" tab
                        let mut hide_subchannels_val = *self.settings.hide_subchannel_from_parent_all.get(&parent_channel).unwrap_or(&false);
                        if ui.checkbox(&mut hide_subchannels_val, "Hide from 'All'").clicked() {
                            self.settings.hide_subchannel_from_parent_all.insert(parent_channel, hide_subchannels_val);
                            save_settings(&self.settings);
                            if let Err(e) = self.settings_sender.send(self.settings.clone()) {
                                eprintln!("Failed to send updated settings to scanner thread: {}", e);
                            }
                        }
                    });
                    
                    ui.separator();
                }
            }


            ScrollArea::vertical().stick_to_bottom(true).show(ui, |ui| {
                for msg in &self.messages {
                    let mut show_message = false;
                    
                    // Filter based on main channel
                    let message_channel = ChatChannel::from_prefix(&msg.prefix).unwrap_or(ChatChannel::Other);
                    
                    // Case 1: "All" global tab is selected
                    if self.selected_channel == "All" {
                        if msg.prefix == "Status" && !self.settings.show_debug_messages {
                            show_message = false;
                        } else if self.settings.hide_subchannel_messages && msg.sub_channel.is_some() {
                             show_message = false;
                        } else {
                            show_message = true;
                        }
                    } 
                    // Case 2: A main channel tab is selected (with potential sub-channels)
                    else if self.selected_channel == message_channel.to_string() {
                        // Now check the sub-channel filter
                        if self.selected_sub_channel == "All" {
                            // "All" sub-tab is selected, apply hide filter if applicable
                            if let Some(hide_filter_enabled) = self.settings.hide_subchannel_from_parent_all.get(&message_channel) {
                                if *hide_filter_enabled && msg.sub_channel.is_some() {
                                    show_message = false;
                                } else {
                                    show_message = true;
                                }
                            } else {
                                show_message = true;
                            }
                        } else {
                            // A specific sub-channel is selected
                            if let Some(msg_sub) = &msg.sub_channel {
                                if msg_sub == &self.selected_sub_channel {
                                    show_message = true;
                                }
                            }
                        }
                    }
                    // Case 3: A custom channel group is selected
                    else if let Some(group) = self.settings.channel_groups.iter().find(|g| g.name == self.selected_channel) {
                        if group.channels.contains(&message_channel) {
                            // Check for excluded sub-channels
                            if let Some(sub_channel) = &msg.sub_channel {
                                if !group.excluded_subchannels.contains(sub_channel) {
                                    show_message = true;
                                }
                            } else {
                                // If no sub-channel, it's not excluded
                                show_message = true;
                            }
                        }
                    }

                    if show_message {
                        let mut message_string = String::new();
                        
                        // Add icons if enabled and applicable
                        if self.settings.show_icons {
                            if msg.do_ding {
                                message_string.push_str("笙ｪ ");
                            }
                            if message_channel == ChatChannel::Items {
                                if GOLD_REGEX.is_match(&msg.content) {
                                    message_string.push_str("腸 ");
                                } else {
                                    message_string.push_str("賜 ");
                                }
                            }
                            if message_channel == ChatChannel::Announce {
                                message_string.push_str("討 ");
                            }
                        }

                        let mut formatted_message_content = format!("{}: {}", msg.prefix, msg.content);
                        if self.settings.timestamp_format != TimestampFormat::None {
                            formatted_message_content = format!("[{}] {}", msg.timestamp, formatted_message_content);
                        }
                        
                        message_string.push_str(&formatted_message_content);

                        // Dynamic rich text for combat numbers
                        if self.settings.shorten_combat_numbers && message_channel == ChatChannel::Combat {
                            // We don't need `rich_text` as a variable here, so it's removed.
                            let mut last_end = 0;
                            let mut found_match = false;

                            for caps in COMBAT_NUMBER_REGEX.captures_iter(&message_string) {
                                if let Some(num_str) = caps.get(1) {
                                    if let Ok(number) = num_str.as_str().parse::<f64>() {
                                        if number >= 1000.0 {
                                            let shortened_number = format!("{:.1}k", number / 1000.0);
                                            let start = caps.get(0).unwrap().start();
                                            let end = caps.get(0).unwrap().end();

                                            ui.horizontal(|ui| {
                                                // Part 1: Text before the number
                                                ui.label(RichText::new(&message_string[last_end..start]).color(msg.color));
                                                // Part 2: The formatted number in orange
                                                ui.label(RichText::new(shortened_number).color(Color32::from_rgb(255, 165, 0)));
                                                // Part 3: Text after the number
                                                ui.label(RichText::new(&message_string[end..]).color(msg.color));
                                            });
                                            last_end = end;
                                            found_match = true;
                                        }
                                    }
                                }
                            }

                            if found_match {
                                // We are done. The whole message has been drawn.
                            } else {
                                ui.label(RichText::new(message_string).color(msg.color));
                            }
                        } else {
                            // Shorten combat numbers is off, display original message
                            ui.label(RichText::new(message_string).color(msg.color));
                        }
                    }
                }
            });
        });

        // Status bar
        if self.settings.show_debug_messages {
            egui::TopBottomPanel::bottom("status_bar").show(ctx, |ui| {
                ui.horizontal(|ui| {
                    ui.label(format!("Messages loaded: {}", self.messages.len()));
                    ui.add_space(ui.available_width() * 0.5);
                    ui.label(format!("Avg Scan Time: {:.2} ms", self.avg_scan_time));
                });
            });
        }
        
        if self.show_settings_window {
            self.draw_settings_window(ctx);
        }
        
        if self.show_channel_group_editor {
            self.draw_channel_group_editor(ctx);
        }

        if self.settings.enable_damage_analyzer && self.show_damage_analyzer_window {
            self.draw_damage_analyzer_window(ctx);
        }

        if self.settings.enable_exp_analyzer && self.show_exp_analyzer_window {
            self.draw_exp_analyzer_window(ctx);
        }
    }
}

fn main() {
    let (msg_sender, msg_receiver) = mpsc::channel();
    let (settings_sender, settings_receiver) = mpsc::channel();
    let (file_dialog_request_tx, file_dialog_request_rx) = mpsc::channel();
    let (file_dialog_response_tx, file_dialog_response_rx) = mpsc::channel();
    
    // Load initial settings from file
    let mut settings = load_settings();
    let settings_for_main_thread = settings.clone(); // Clone settings for the UI thread
    
    // Find all Grand Fantasia processes
    let available_pids = find_all_pids_by_name(PROCESS_NAME).unwrap_or_else(|e| {
        eprintln!("Error finding processes: {}", e);
        Vec::new()
    });

    if let Some(pid_to_use) = settings.selected_pid {
        if !available_pids.iter().any(|(p, _)| p.as_u32() == pid_to_use) {
            println!("Saved PID {} not found. Using first available PID.", pid_to_use);
            settings.selected_pid = available_pids.first().map(|(p, _)| p.as_u32());
        }
    } else {
        settings.selected_pid = available_pids.first().map(|(p, _)| p.as_u32());
    }

    // Spawn the memory scanning thread
    let scanner_pid = settings.selected_pid;
    thread::spawn(move || {
        let ac = AhoCorasick::new(CHAT_PREFIXES).unwrap();
        // This set now tracks all found addresses across scans. Messages are only sent to the UI
        // if their address is new.
        let mut found_addresses: HashSet<usize> = HashSet::new();
        let mut current_settings = settings;

        let pid = match scanner_pid {
            Some(p) => p,
            None => {
                eprintln!("No process selected to scan.");
                return;
            }
        };

        let process_handle = unsafe { OpenProcess(PROCESS_QUERY_INFORMATION | PROCESS_VM_READ, 0, pid) };
        if process_handle.is_null() {
            eprintln!("Failed to open process. Make sure you have the necessary permissions.");
            return;
        }

        let mut log_file = OpenOptions::new()
            .create(true)
            .write(true)
            .append(true)
            .open("chat_log.txt")
            .expect("Failed to open or create log file");
    
        println!("Scanning memory for chat prefixes...");

        let mut is_first_scan = true;
    
        loop {
            // Check for updated settings from the UI thread
            if let Ok(new_settings) = settings_receiver.try_recv() {
                current_settings = new_settings;
                println!("Scanner thread received new settings.");
            }
            
            // Check log file size and truncate if necessary
            if let Ok(metadata) = metadata("chat_log.txt") {
                if metadata.len() > current_settings.log_file_size_limit_mb * 1024 * 1024 {
                    if let Err(e) = log_file.set_len(0) {
                        eprintln!("Failed to truncate log file: {}", e);
                    }
                    if let Err(e) = log_file.seek(SeekFrom::Start(0)) {
                        eprintln!("Failed to seek log file: {}", e);
                    }
                    println!("Log file truncated to 0 bytes.");
                }
            }
            
            let start_time = Instant::now();
            let mut address = 0usize;
    
            // This set is used to de-duplicate messages found in the current scan.
            // It is cleared on each new scan to allow the same message content to appear if it's new.
            let mut newly_found_messages: HashSet<String> = HashSet::new();
            let mut new_messages_count = 0;

            unsafe {
                let mut mem_info: MEMORY_BASIC_INFORMATION = mem::zeroed();
    
                while VirtualQueryEx(process_handle, address as LPVOID, &mut mem_info, mem::size_of::<MEMORY_BASIC_INFORMATION>()) != 0 {
                    let protect = mem_info.Protect;
                    let region_base = mem_info.BaseAddress as usize;
                    let region_size = mem_info.RegionSize;
    
                    if mem_info.State == winapi::um::winnt::MEM_COMMIT && (protect == PAGE_READWRITE) {
                        let mut buffer = vec![0u8; region_size];
                        let mut bytes_read = 0;
    
                        if ReadProcessMemory(
                            process_handle,
                            region_base as LPCVOID,
                            buffer.as_mut_ptr() as LPVOID,
                            region_size,
                            &mut bytes_read,
                        ) != 0 {
                            let readable_buffer = &buffer[..bytes_read as usize];
    
                            for mat in ac.find_iter(readable_buffer) {
                                let found_address = region_base + mat.start();
                                
                                // Only process messages if their address is new.
                                if found_addresses.insert(found_address) {
                                    let prefix = CHAT_PREFIXES[mat.pattern()];
    
                                    let full_string = read_zero_terminated_string(process_handle, found_address);

                                    // Heuristic check: if the string is too long, it's likely a false positive.
                                    if full_string.len() > 512 {
                                        if current_settings.show_debug_messages {
                                            eprintln!("Skipping potential false positive due to excessive length at address 0x{:X}", found_address);
                                        }
                                        continue;
                                    }

                                    let mut trimmed_string = full_string;
                                    if trimmed_string.starts_with(prefix) {
                                        trimmed_string = trimmed_string[prefix.len()..].trim().to_string();
                                    }
                                    
                                    // Deduplicate based on the message content within this specific scan.
                                    // This prevents logging duplicates that appear within a single scan interval.
                                    if newly_found_messages.insert(trimmed_string.clone()) {
                                        new_messages_count += 1;
                                        
                                        // Determine sub-channel
                                        let mut sub_channel_name = None;
                                        let parent_channel = ChatChannel::from_prefix(prefix).unwrap_or(ChatChannel::Other);
                                        if let Some(sub_channels) = SUB_CHANNELS.get(&parent_channel) {
                                            for sub_channel in sub_channels {
                                                if sub_channel.regex.is_match(&trimmed_string) {
                                                    sub_channel_name = Some(sub_channel.name.to_string());
                                                    break;
                                                }
                                            }
                                        }
    
                                        let full_message = format!("{}: {}", prefix, trimmed_string);
                                        
                                        let timestamp = Local::now();
                                        let log_entry = format!("[{}] {}\n", timestamp.format("%Y-%m-%d %H:%M:%S").to_string(), full_message);
                                        if let Err(e) = log_file.write_all(log_entry.as_bytes()) {
                                            eprintln!("Failed to write to log file: {}", e);
                                        }
                                        
                                        let color_rgba = current_settings.channel_colors.get(&parent_channel).cloned().unwrap_or([0xFF, 0xFF, 0xFF, 0xFF]);
                                        let color = Color32::from_rgba_unmultiplied(color_rgba[0], color_rgba[1], color_rgba[2], color_rgba[3]);
                                        
                                        let do_ding = if let Some(sub_channel_name_str) = &sub_channel_name {
                                            *current_settings.subchannel_audio.get(sub_channel_name_str).unwrap_or(&false)
                                        } else {
                                            *current_settings.channel_audio.get(&parent_channel).unwrap_or(&false)
                                        };
                                        
                                        let msg = ChatMessage {
                                            prefix: prefix.to_string(),
                                            content: trimmed_string.clone(),
                                            address: found_address,
                                            sub_channel: sub_channel_name,
                                            color,
                                            do_ding,
                                            timestamp: current_settings.timestamp_format.format_timestamp(&timestamp),
                                            raw_content: Some(full_message),
                                        };
                                        if let Err(e) = msg_sender.send(msg) {
                                            eprintln!("Failed to send message to UI thread: {}", e);
                                        }
                                    }
                                }
                            }
                        }
                    }
    
                    address += region_size;
                    if address == 0 {
                        break;
                    }
                }
            }
    
            let duration = start_time.elapsed();

            // Send a status message after the first scan to trigger `is_first_scan_done`
            if is_first_scan {
                if let Err(e) = msg_sender.send(ChatMessage {
                    prefix: "Status".to_string(),
                    content: format!("Initial scan complete. Found {} messages.", newly_found_messages.len()),
                    address: 0,
                    sub_channel: Some("System".to_string()),
                    color: Color32::GRAY,
                    do_ding: false,
                    timestamp: Local::now().format("%H:%M:%S").to_string(),
                    raw_content: None,
                }) {
                    eprintln!("Failed to send status message to UI thread: {}", e);
                }
                is_first_scan = false;
            }

            if current_settings.show_debug_messages {
                if let Err(e) = msg_sender.send(ChatMessage {
                    prefix: "Status".to_string(),
                    content: format!("Scan complete. Found {} new results in {:?}.", new_messages_count, duration),
                    address: 0,
                    sub_channel: Some("System".to_string()),
                    color: Color32::GRAY,
                    do_ding: false,
                    timestamp: Local::now().format("%H:%M:%S").to_string(),
                    raw_content: None,
                }) {
                    eprintln!("Failed to send status message to UI thread: {}", e);
                }
            }
            
            thread::sleep(Duration::from_millis(current_settings.scan_interval_ms));
        }
    });

    // Spawn a new thread to handle the file dialog requests.
    thread::spawn(move || {
        while let Ok((channel_type, subchannel_name)) = file_dialog_request_rx.recv() {
            let path = FileDialog::new()
                .add_filter("Audio Files", &["wav", "mp3", "flac"])
                .pick_file();
            if let Err(e) = file_dialog_response_tx.send((channel_type, subchannel_name, path)) {
                eprintln!("Failed to send file dialog result: {}", e);
            }
        }
    });

    // Create an audio output stream and sink
    let (_stream, _stream_handle) = OutputStream::try_default().expect("Failed to create audio output stream");
    let sink = Sink::try_new(&_stream_handle).expect("Failed to create audio sink");
    
    // Set up the Egui application
    let native_options = eframe::NativeOptions {
        viewport: egui::ViewportBuilder::default()
            .with_inner_size(egui::vec2(1300.0, 1000.0))
            .with_always_on_top(),
        ..Default::default()
    };
    eframe::run_native(
        "Grand Fantasia Chat Logger",
        native_options,
        Box::new(|_cc| Box::new(ChatLoggerApp::new(msg_receiver, settings_sender, available_pids, settings_for_main_thread, _stream, sink, file_dialog_request_tx, file_dialog_response_rx))),
    ).expect("Failed to run UI application");
}
