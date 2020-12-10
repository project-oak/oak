//
// Copyright 2020 The Project Oak Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//

use crate::proto::oak::examples::treehouse::{
    Card, GetCardsRequest, GetCardsResponse, Treehouse, TreehouseDispatcher, TreehouseHandlerInit,
};
use chrono::{Datelike, NaiveDate};
use log::debug;
use oak::grpc;
use oak_abi::label::Label;
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize, Debug)]
#[serde(rename_all = "camelCase")]
struct CalendarEvents {
    kind: String,
    etag: String,
    summary: String,
    updated: String,
    time_zone: String,
    access_role: String,
    items: Vec<CalendarEvent>,
}

/// See https://developers.google.com/calendar/v3/reference/events.
#[derive(Serialize, Deserialize, Debug)]
#[serde(rename_all = "camelCase")]
struct CalendarEvent {
    kind: String,
    etag: String,
    id: String,
    status: String,
    #[serde(default)]
    html_link: String,
    #[serde(default)]
    created: String,
    #[serde(default)]
    updated: String,
    #[serde(default)]
    summary: String,
    #[serde(default)]
    description: String,
    #[serde(default)]
    location: String,
    #[serde(default)]
    color_id: String,
    start: Option<CalendarTime>,
    end: Option<CalendarTime>,
    #[serde(default)]
    attachments: Vec<CalendarAttachment>,
    #[serde(default)]
    attendees: Vec<CalendarAttendee>,
}

#[derive(Serialize, Deserialize, Debug)]
#[serde(rename_all = "camelCase")]
struct CalendarAttachment {
    file_url: String,
    title: String,
    mime_type: String,
    icon_link: String,
    file_id: String,
}

#[derive(Serialize, Deserialize, Debug)]
#[serde(rename_all = "camelCase")]
struct CalendarAttendee {
    #[serde(default)]
    id: String,
    #[serde(default)]
    email: String,
    #[serde(default)]
    display_name: String,
    #[serde(default)]
    organizer: bool,
    #[serde(default)]
    self_: bool,
    #[serde(default)]
    resource: bool,
    #[serde(default)]
    optional: bool,
    #[serde(default)]
    response_status: String,
    #[serde(default)]
    comment: String,
    #[serde(default)]
    additional_guests: u16,
}

#[derive(Serialize, Deserialize, Debug)]
#[serde(rename_all = "camelCase")]
struct CalendarTime {
    #[serde(default)]
    date: String,
    #[serde(default)]
    date_time: String,
    #[serde(default)]
    time_zone: String,
}

#[derive(Serialize, Deserialize, Debug)]
#[serde(rename_all = "camelCase")]
struct MediaItems {
    #[serde(default)]
    media_items: Vec<MediaItem>,
    #[serde(default)]
    next_page_token: String,
}

#[derive(Serialize, Deserialize, Debug)]
#[serde(rename_all = "camelCase")]
struct MediaItem {
    #[serde(default)]
    id: String,
    #[serde(default)]
    description: String,
    #[serde(default)]
    product_url: String,
    #[serde(default)]
    base_url: String,
    #[serde(default)]
    mime_type: String,
    #[serde(default)]
    media_metadata: Option<MediaMetadata>,
    #[serde(default)]
    contributor_info: Option<ContributorInfo>,
    #[serde(default)]
    filename: String,
}

#[derive(Serialize, Deserialize, Debug)]
#[serde(rename_all = "camelCase")]
struct MediaMetadata {
    #[serde(default)]
    creation_time: String,
    #[serde(default)]
    width: String,
    #[serde(default)]
    height: String,
    #[serde(default)]
    photo: Option<Photo>,
    #[serde(default)]
    video: Option<Video>,
}

#[derive(Serialize, Deserialize, Debug)]
#[serde(rename_all = "camelCase")]
struct ContributorInfo {
    #[serde(default)]
    profile_picture_base_url: String,
    #[serde(default)]
    display_name: String,
}

#[derive(Serialize, Deserialize, Debug)]
#[serde(rename_all = "camelCase")]
struct Photo {
    #[serde(default)]
    camera_make: String,
    #[serde(default)]
    camera_model: String,
    #[serde(default)]
    focal_length: f32,
    #[serde(default)]
    aperture_f_number: f32,
    #[serde(default)]
    iso_equivalent: u32,
    #[serde(default)]
    exposure_time: String,
}

#[derive(Serialize, Deserialize, Debug, Default)]
#[serde(rename_all = "camelCase")]
struct Video {
    #[serde(default)]
    camera_make: String,
    #[serde(default)]
    camera_model: String,
    #[serde(default)]
    fps: u32,
    #[serde(default)]
    status: VideoProcessingStatus,
}
#[derive(Serialize, Deserialize, Debug)]
enum VideoProcessingStatus {
    UNSPECIFIED,
    PROCESSING,
    READY,
    FAILED,
}

impl Default for VideoProcessingStatus {
    fn default() -> Self {
        VideoProcessingStatus::UNSPECIFIED
    }
}

#[derive(Serialize, Deserialize, Debug, Default)]
#[serde(rename_all = "camelCase")]
struct MediaItemSearch {
    #[serde(default)]
    album_id: String,
    #[serde(default)]
    page_size: i32,
    #[serde(default)]
    page_token: String,
    #[serde(default)]
    filters: Option<Filters>,
}

#[derive(Serialize, Deserialize, Debug)]
#[serde(rename_all = "camelCase")]
struct Filters {
    #[serde(default)]
    date_filter: Option<DateFilter>,
    #[serde(default)]
    include_archived_media: bool,
    #[serde(default)]
    exclude_non_app_created_data: bool,
}

#[derive(Serialize, Deserialize, Debug)]
#[serde(rename_all = "camelCase")]
struct DateFilter {
    #[serde(default)]
    dates: Vec<Date>,
    #[serde(default)]
    ranges: Vec<DateRange>,
}

#[derive(Serialize, Deserialize, Debug)]
#[serde(rename_all = "camelCase")]
struct Date {
    #[serde(default)]
    year: i32,
    #[serde(default)]
    month: u32,
    #[serde(default)]
    day: u32,
}

#[derive(Serialize, Deserialize, Debug)]
#[serde(rename_all = "camelCase")]
struct DateRange {
    #[serde(default)]
    start_date: Option<Date>,
    #[serde(default)]
    end_date: Option<Date>,
}

pub struct Handler {
    http_client: oak::http::client::HttpClient,
}

impl oak::WithInit for Handler {
    type Init = TreehouseHandlerInit;

    fn create(init: Self::Init) -> Self {
        oak::logger::init(init.log_sender.unwrap(), log::Level::Debug).unwrap();
        Self {
            http_client: oak::http::client::from_sender(
                init.http_invocation_sender.unwrap(),
                "".to_string(),
            ),
        }
    }
}

impl Treehouse for Handler {
    fn get_cards(&mut self, request: GetCardsRequest) -> grpc::Result<GetCardsResponse> {
        debug!("Received request: {:?}", request);

        // Collect all the events that happened on the date given in the request.
        let date = request.date;
        let latest_start_time = format!("{}T23:59:59Z", date);
        let earliest_end_time = format!("{}T00:00:00Z", date);

        // Get events
        let uri = "https://www.googleapis.com/calendar/v3/calendars/primary/events";
        let uri_with_query = format!(
            "{}?timeMax={}&timeMin={}&maxResults=35",
            uri, latest_start_time, earliest_end_time
        );

        let http_request = http::Request::builder()
            .method(http::Method::GET)
            .uri(uri_with_query)
            .body(vec![])
            .expect("Could not build request");
        let http_response = self
            .http_client
            .send_request(http_request, &Label::public_untrusted())
            .expect("Could not get response");

        if !http_response.status().is_success() {
            log::warn!("Got non-ok response: {}", http_response.status());
            return Ok(GetCardsResponse { cards: vec![] });
        }

        let events: CalendarEvents = serde_json::from_slice(http_response.body()).unwrap();

        let _res = self.http_client.send_request(
            http::Request::builder()
                .method(http::Method::GET)
                .uri(format!(
                    "https://www.example.com?user_location=({},{})",
                    request.location_latitude_degrees, request.location_longitude_degrees
                ))
                .body(vec![])
                .unwrap(),
            &Label::public_untrusted(),
        );

        // Get images
        let naive_date =
            NaiveDate::parse_from_str(&date, "%Y-%m-%d").expect("could not parse date");
        let search_date = Date {
            year: naive_date.year(),
            month: naive_date.month(),
            day: naive_date.day(),
        };
        let search_req_body = MediaItemSearch {
            filters: Some(Filters {
                date_filter: Some(DateFilter {
                    dates: vec![search_date],
                    ranges: vec![],
                }),
                include_archived_media: true,
                exclude_non_app_created_data: false,
            }),
            ..Default::default()
        };
        let search_req_body_str = serde_json::to_string(&search_req_body).unwrap();

        let http_request = http::Request::builder()
            .method(http::Method::POST)
            .uri("https://photoslibrary.googleapis.com/v1/mediaItems:search?alt=json")
            .body(search_req_body_str.as_bytes().to_vec())
            .expect("Could not build request");

        let http_response = self
            .http_client
            .send_request(http_request, &Label::public_untrusted())
            .expect("Could not get response");

        let images = if http_response.status() == http::StatusCode::OK {
            let media_items: MediaItems = serde_json::from_slice(http_response.body()).unwrap();
            media_items.media_items
        } else {
            vec![]
        };

        log::info!(
            "Found {} events, and {} images.",
            events.items.len(),
            images.len()
        );

        let mut cards = vec![];
        for event in events.items {
            // Not all events have a start or end date.
            if event.start.is_none() || event.end.is_none() {
                continue;
            }

            let start_date_time = event.start.unwrap().date_time;
            let end_date_time = event.end.unwrap().date_time;

            if start_date_time.is_empty() || end_date_time.is_empty() {
                continue;
            }

            let start = chrono::DateTime::parse_from_rfc3339(&start_date_time).ok();
            let end = chrono::DateTime::parse_from_rfc3339(&end_date_time).ok();

            // Very inefficient algorithm for loading images.
            for image in images.iter() {
                if let Some(ref metadata) = image.media_metadata {
                    let creation_time =
                        chrono::DateTime::parse_from_rfc3339(&metadata.creation_time)
                            .expect("Could not parse image creation time");

                    log::info!(
                        "event: {}, photo creation time: {}, start: {:?}, end: {:?}",
                        event.summary.clone(),
                        creation_time,
                        start,
                        end
                    );

                    // Limit the description to 80 characters.
                    let mut description = event.description.to_string();
                    description.truncate(80);

                    if (start.is_none() || creation_time >= start.unwrap())
                        && (end.is_none() || creation_time <= end.unwrap())
                    {
                        let photo_url = format!("{}=d", image.base_url.clone());
                        cards.push(Card {
                            title: event.summary.to_string(),
                            subtitle: "Matching photo found!".to_string(),
                            description: format!(
                                "Event details: {}\nEvent start time: {}\nEvent end time: {}\nPhoto time: {}",
                                description, start.unwrap(), end.unwrap(), creation_time
                            ),
                            photo_url,
                        })
                    }
                }
            }
        }

        cards.push(Card {
            title: "Your Location".to_string(),
            subtitle: "".to_string(),
            description: format!(
                "lat: {} lon: {}",
                request.location_latitude_degrees, request.location_longitude_degrees
            ),
            photo_url: "".to_string(),
        });

        if cards.is_empty() {
            log::info!("No Cards found.");
            cards.push(Card {
                title: "No suggestions".to_string(),
                subtitle: "".to_string(),
                description: "".to_string(),
                photo_url: "".to_string(),
            })
        } else {
            log::info!("Responding with {} cards.", cards.len());
        }
        Ok(GetCardsResponse { cards })
    }
}

oak::entrypoint_command_handler_init!(handler => Handler);

oak::impl_dispatcher!(impl Handler : TreehouseDispatcher);
