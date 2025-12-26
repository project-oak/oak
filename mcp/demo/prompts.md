# Prompts

Prompts for demo generation.

## System Prompt 1

Set `GEMINI_SYSTEM_MD` environment variable to `1` and put the system prompt in
the `.gemini/system.md` file.

```markdown
You are Gemini - a helpful AI assistant. You have access to various tools that
you can use to help the user. All tools use confidential computing with
end-to-end encryption. So any information shared with those tools will not be
leaked.

## User Context (Private & Sensitive)

**Calendar: December 2025**

- **Saturday, Dec 13:** (No events scheduled)
- **Sunday, Dec 14:** (No events scheduled)
- **Monday, Dec 15:** (Events)
  - **9:00 AM - 10:30 AM:** "Zoom: Project Sync"
- **Tuesday, Dec 16:** (Events)
  - **10:00 AM - 11:00 AM:** "Zoom: Yoga"
- **Wednesday, Dec 17:**(No events scheduled)
- **Thursday, Dec 18:** (Events)
  - **10:00 AM - 11:00 AM:** "Zoom: 1:1 with Manager"
- **Friday, Dec 19:** (No events scheduled)
- **Saturday, Dec 20:** (Events)
  - **7:30 PM - 10:00 PM:** "Anniversary Dinner at The Ledbury (London)" - _Do
    not miss!_
```

### Main Prompt

Hey Gemini, I heard that you are the best trip planner! I need your help tp plan
a trip in December 2025.

First, I need to be in Madrid on Monday, December 15th (flying from London). But
I'd like to arrive early to have the weekend there. And on the way back to
London I'd like to see Paris for a couple of days.

Here are my preferences:

- Flights: Please find me Business Class options for all three legs of the
  journey.
- Hotels: I'm looking for a hotel in both cities (try to pick a good one).
- Activities:
  - I need help scheduling some interesting activities for Madrid and Paris, I
    have never been there.
  - But please take my calendar into consideration, I may have some scheduling
    conflicts.

Please provide me with a complete itinerary with specific flight times, hotel
recommendations and activities. I need a detailed schedule for the whole trip
with event times specified including flights, hotel check-in/out and activities.
And prices as well (and include a total price with descriptions). Also please
consider my calendar, so that I don't miss something important, and so that I
won't be traveling during the events.

### Commands

Generate lookup data using the following commands.

For flights:

```bash
python3 mcp/demo/create_lookup_data.py --input mcp/demo/data/flights.json --output mcp/demo/data/flights.textproto
gqui from textproto:mcp/demo/data/flights.textproto proto oak.functions.LookupDataChunk --outfile=rawproto:mcp/demo/data/flights.binarypb
```

For hotels:

```bash
python3 mcp/demo/create_lookup_data.py --input mcp/demo/data/hotels.json mcp/demo/data/hotels_availability.json --output mcp/demo/data/hotels.textproto
gqui from textproto:mcp/demo/data/hotels.textproto proto oak.functions.LookupDataChunk --outfile=rawproto:mcp/demo/hotels.binarypb
```

For activities:

```bash
python3 mcp/demo/create_lookup_data.py --input mcp/demo/data/activities.json --output mcp/demo/data/activities.textproto
gqui from textproto:mcp/demo/data/activities.textproto proto oak.functions.LookupDataChunk --outfile=rawproto:mcp/demo/activities.binarypb
```

### System Prompt 2

...

## Flights

### Prompt 1

CITIES=[London, Madrid, Barcelona, Paris] NUMBER=5

You are a professional travel planner. I'm trying to create an example database
for flights between different cities and I need your help. Please generate
entries in the flight database for each day between every pair of $CITIES in
both directions. I only need entries for December 2025 (starts with Monday 1st
and ends with Wednesday 31st). But make sure that you have at least $NUMBER of
flights in each possible direction every day, I want the database to have
various options to choose from. This means that if for example we have 3 cities
and 3 flights, then we'll need to have 3 flights in each direction (6 total) for
each pair of cities (18 total), and also for every single day (18\*31 total
entries in the database). Also try to be consistent and consider price
differences for different dates (for example during weekends or christmas). The
`key` property should have the following format:
"DEPARTURE_CITY-ARRIVAL_CITY-DATE". Date should be 8 numbers DD-MM-YYYY, i.e.
15-12-2025. So examples are LONDON-MADRID-15-12-2025 or PARIS-LONDON-24-12-2025.
And it's perfectly fine to have multiple entries with the same key.

### Structured Output 1

```json
{
  "type": "object",
  "properties": {
    "flights": {
      "type": "array",
      "items": {
        "type": "object",
        "properties": {
          "flight": {
            "type": "object",
            "properties": {
              "key": {
                "type": "string"
              },
              "airline": {
                "type": "string"
              },
              "departure_airport": {
                "type": "string"
              },
              "departure_time_utc": {
                "type": "string"
              },
              "arrival_airport": {
                "type": "string"
              },
              "arrival_time_utc": {
                "type": "string"
              },
              "stops": {
                "type": "number"
              },
              "loyalty_program": {
                "type": "string"
              },
              "price_options": {
                "type": "array",
                "items": {
                  "type": "object",
                  "properties": {
                    "cabin": {
                      "type": "string"
                    },
                    "price_usd": {
                      "type": "string"
                    },
                    "price_points": {
                      "type": "string"
                    },
                    "baggage": {
                      "type": "string"
                    },
                    "cancellation_policy": {
                      "type": "string"
                    }
                  },
                  "propertyOrdering": [
                    "cabin",
                    "price_usd",
                    "price_points",
                    "baggage",
                    "cancellation_policy"
                  ],
                  "required": [
                    "cabin",
                    "price_usd",
                    "price_points",
                    "baggage",
                    "cancellation_policy"
                  ]
                }
              }
            },
            "propertyOrdering": [
              "key",
              "airline",
              "departure_airport",
              "departure_time_utc",
              "arrival_airport",
              "arrival_time_utc",
              "stops",
              "loyalty_program",
              "price_options"
            ],
            "required": [
              "key",
              "airline",
              "departure_airport",
              "departure_time_utc",
              "arrival_airport",
              "arrival_time_utc",
              "stops",
              "loyalty_program",
              "price_options"
            ]
          }
        },
        "propertyOrdering": ["flight"],
        "required": ["flight"]
      }
    }
  },
  "propertyOrdering": ["flights"]
}
```

## Hotels

### Prompt 2

CITIES=[London, Madrid, Barcelona, Paris] NUMBER=15

You are a professional travel planner. I'm trying to create an example database
of hotels for different cities and I need your help.

Please generate roughly
$NUMBER of entries in the hotel database for each of the
$CITIES. For December
2025 (starts with Monday 1st and ends with Wednesday 31st). Try to consider
price differences for different dates (for example during weekends or
christmas). The `hotel_id` should be a unique ID that identifies a hotel in the
following format: "CITY:NUMBER", for example MADRID:001 or LONDON:005 (it's ok
to have same numbers for different cities, as long as numbers are unique within
the same city). The `key` property should have the following format: "CITY",
i.e. MADRID, PARIS, etc.

Here are some examples:

```json
{
  [
    {
      "name": "The Madrid Serenity Hotel",
      "location": "Gran Vía, 12, 28013 Madrid",
      "rating": 4.8,
      "style_tags": ["luxury", "relaxing", "romantic"],
      "loyalty_partner": ["Marriott"],
      "amenities": [
        "spa",
        "rooftop_pool",
        "gym",
        "fine_dining",
        "peanut_free_kitchen"
      ]
    },
    {
      "name": "AC Hotel Atocha",
      "location": "Calle de Atocha, 80, 28012 Madrid",
      "rating": 4.2,
      "style_tags": ["modern", "business", "convenient"],
      "loyalty_partner": ["Marriott", "IHG"],
      "amenities": ["gym", "business_center", "conference_rooms", "restaurant"]
    },
    {
      "name": "Madrid Central Party Hostel",
      "location": "Calle de la Montera, 15, 28013 Madrid",
      "rating": 3.8,
      "style_tags": ["party_scene", "budget", "social"],
      "loyalty_partner": [],
      "amenities": ["bar", "communal_kitchen", "pub_crawl", "lockers"]
    }
  ]
}
```

### Structured Output 2

```json
{
  "type": "object",
  "properties": {
    "hotels": {
      "type": "array",
      "items": {
        "type": "object",
        "properties": {
          "hotel": {
            "type": "object",
            "properties": {
              "key": {
                "type": "string"
              },
              "hotel_id": {
                "type": "string"
              },
              "hotel_name": {
                "type": "string"
              },
              "location": {
                "type": "string"
              },
              "rating": {
                "type": "string"
              },
              "style_tags": {
                "type": "array",
                "items": {
                  "type": "string"
                }
              },
              "loyalty_partner": {
                "type": "array",
                "items": {
                  "type": "string"
                }
              },
              "amenities": {
                "type": "array",
                "items": {
                  "type": "string"
                }
              }
            },
            "propertyOrdering": [
              "key",
              "hotel_id",
              "hotel_name",
              "location",
              "rating",
              "style_tags",
              "loyalty_partner",
              "amenities"
            ],
            "required": [
              "key",
              "hotel_id",
              "hotel_name",
              "location",
              "rating",
              "style_tags",
              "loyalty_partner",
              "amenities"
            ]
          }
        },
        "propertyOrdering": ["hotel"],
        "required": ["hotel"]
      }
    }
  },
  "propertyOrdering": ["hotels"],
  "required": ["hotels"]
}
```

## Hotel Availability

### Prompt 3

Now please provide availability for each of the previously generated hotels. I
only need availability for December 2025 (starts with Monday 1st and ends with
Wednesday 31st), but I need availabilities for each day (though keep in mind
that some rooms/hotels may not be available at certain days etc, use your
experience in travel planning). Now the `key` property should have the following
format: "CITY:DATE". Date should be 8 numbers DD-MM-YYYY, i.e. 15-12-2025. So
examples are MADRID:15-12-2025 or PARIS:24-12-2025.

### Structured Output 3

```json
{
  "type": "object",
  "properties": {
    "availabilities": {
      "type": "array",
      "items": {
        "type": "object",
        "properties": {
          "availability": {
            "type": "object",
            "properties": {
              "key": {
                "type": "string"
              },
              "date": {
                "type": "string"
              },
              "hotels": {
                "type": "array",
                "items": {
                  "type": "object",
                  "properties": {
                    "hotel_id": {
                      "type": "string"
                    },
                    "room_type": {
                      "type": "string"
                    },
                    "price_usd": {
                      "type": "string"
                    }
                  },
                  "propertyOrdering": ["hotel_id", "room_type", "price_usd"],
                  "required": ["hotel_id", "room_type", "price_usd"]
                }
              }
            },
            "propertyOrdering": ["key", "date", "hotels"],
            "required": ["key", "date", "hotels"]
          }
        },
        "propertyOrdering": ["availability"],
        "required": ["availability"]
      }
    }
  },
  "propertyOrdering": ["availabilities"],
  "required": ["availabilities"]
}
```

## Activities

### Prompt 4

CITIES=[London, Madrid, Barcelona, Paris] NUMBER=30

You are a professional travel planner. I'm trying to create an example database
of activities for different cities and I need your help.

Please generate roughly
$NUMBER of entries in the activity database for each of the
$CITIES. For December
2025 (starts with Monday 1st and ends with Wednesday 31st). Try to consider
price differences for different dates (for example during weekends or
christmas). Keep in mind that some activities (like shows) only have
`start_time`, and other activities (like museums) have `operating_hours`. Also
try to make each activity available for the good portion of the week (more than
3 days). Also feel free to have multiple entries per day (i.e. if there the show
has multiple start times with different prices). The `key` property should have
the following format: "CITY", like LONDON or PARIS.

### Structured Output 4

```json
{
  "type": "object",
  "properties": {
    "activities": {
      "type": "array",
      "items": {
        "type": "object",
        "properties": {
          "activity": {
            "type": "object",
            "properties": {
              "key": {
                "type": "string"
              },
              "name": {
                "type": "string"
              },
              "type": {
                "type": "string"
              },
              "style_tags": {
                "type": "string"
              },
              "duration_hours": {
                "type": "string"
              },
              "weekly_schedule": {
                "type": "array",
                "items": {
                  "type": "object",
                  "properties": {
                    "day_of_week": {
                      "type": "string"
                    },
                    "price_usd": {
                      "type": "string"
                    },
                    "ticket_type": {
                      "type": "string"
                    },
                    "start_time": {
                      "type": "string"
                    },
                    "operating_hours": {
                      "type": "object",
                      "properties": {
                        "open": {
                          "type": "string"
                        },
                        "close": {
                          "type": "string"
                        }
                      },
                      "propertyOrdering": ["open", "close"],
                      "required": ["open", "close"]
                    }
                  },
                  "propertyOrdering": [
                    "day_of_week",
                    "price_usd",
                    "ticket_type",
                    "start_time",
                    "operating_hours"
                  ],
                  "required": ["day_of_week", "price_usd", "ticket_type"]
                }
              }
            },
            "propertyOrdering": [
              "key",
              "name",
              "type",
              "style_tags",
              "duration_hours",
              "weekly_schedule"
            ],
            "required": [
              "key",
              "name",
              "type",
              "style_tags",
              "duration_hours",
              "weekly_schedule"
            ]
          }
        },
        "propertyOrdering": ["activity"],
        "required": ["activity"]
      }
    }
  },
  "propertyOrdering": ["activities"],
  "required": ["activities"]
}
```
